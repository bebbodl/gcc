/* Bebbo's Optimizations.
 Copyright (C) 2010-2017 Free Software Foundation, Inc.
 Copyright (C) 2017 Stefan "Bebbo" Franke.

 This file is part of GCC.

 GCC is free software; you can redistribute it and/or modify it under
 the terms of the GNU General Public License as published by the Free
 Software Foundation; either version 3, or (at your option) any later
 version.

 GCC is distributed in the hope that it will be useful, but WITHOUT ANY
 WARRANTY; without even the implied warranty of MERCHANTABILITY or
 FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 for more details.

 You should have received a copy of the GNU General Public License
 along with GCC; see the file COPYING3.  If not see
 <http://www.gnu.org/licenses/>.  */

/**
 * SBF (Stefan "Bebbo" Franke):
 *
 * This pass performs multiple optimizations.
 *
 * #1 propagate_moves
 * check if a->b->a can be moved out of a loop.
 *
 * #2 strcpy
 * check if a temp reg can be eliminated.
 *
 * #3 const_comp_sub
 * convert a compare with int constant into sub statement.
 *
 * #4 merge_add
 * merge adds
 *
 * #5 elim_dead_assign
 * eliminate some dead assignments.
 *
 * #6 shrink stack frame
 * remove push/pop for unused variables
 *
 * #7 rename register
 * rename registers without breaking register parameters, inline asm etc.
 *
 * Lessons learned:
 *
 * - do not trust existing code, better delete insns and inster a new one.
 * - do not modify insns, create new insns from pattern
 * - do not reuse registers, create new reg rtx instances
 *
 */

#include "config.h"
#define INCLUDE_VECTOR
#define INCLUDE_SET
#define INCLUDE_MAP
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "target.h"
#include "rtl.h"
#include "tree.h"
#include "cfghooks.h"
#include "df.h"
#include "memmodel.h"
#include "tm_p.h"
#include "insn-config.h"
#include "regs.h"
#include "stringpool.h"
#include "attribs.h"
#include "tm_p.h"
#include "recog.h"
#include "cfgrtl.h"
#include "emit-rtl.h"
#include "tree-pass.h"
#include "conditions.h"
#include "langhooks.h"
#include "output.h"
#include <vector>
#include <set>
#include <map>

//#define XUSE(c) fputc(c, stderr)
#define XUSE(c) done = 0

int be_very_verbose;
bool be_verbose;

bool optimize_this_for_speed_p;
extern bool
optimize_function_for_speed_p (struct function *fun);

extern struct lang_hooks lang_hooks;

static void
update_insn_infos (void);
static unsigned
track_regs ();

/* Lookup of the current function name. */
extern tree current_function_decl;
static tree last_function_decl;
static char fxname[512];
static char const *
get_current_function_name ()
{
  if (current_function_decl == NULL)
    strcpy (fxname, "<toplevel>");
  else
    strncpy (fxname, lang_hooks.decl_printable_name (current_function_decl, 2), 511);
  return fxname;
}

/* a simple log to stdout. */
static int
log (char const * fmt, ...)
{
  if (!be_verbose)
    return 0;

  va_list args;
  va_start(args, fmt);
  if (last_function_decl != current_function_decl)
    {
      last_function_decl = current_function_decl;
      printf (":bbb: in '%s'\n", get_current_function_name ());
    }
  printf (":bbb: ");
  int retval = vprintf (fmt, args);
  va_end(args);
  fflush (stdout);
  return retval;
}

enum proepis
{
  IN_CODE, IN_PROLOGUE, IN_EPILOGUE, IN_EPILOGUE_PARALLEL_POP
};

/**
 * What's needed to track values?
 */
class track_var
{
  /** The cached value.
   * CONST_INT: if < 0x100000000: a real int value
   *            else: a value encoded from the line where the value was created.
   * MEM: the rtx
   */
  rtx value[FIRST_PSEUDO_REGISTER];

  /*
   * the bitmask of the used registers. needed for invalidation.
   */
  unsigned usedRegs[FIRST_PSEUDO_REGISTER];

  /**
   * contains the bits containing a value.
   */
  unsigned andMask[FIRST_PSEUDO_REGISTER];

  bool
  extend (rtx * z, machine_mode dstMode, rtx x)
  {
    switch (GET_CODE(x))
      {
      case CONST_INT:
      case CONST_FIXED:
      case CONST_DOUBLE:
      case SYMBOL_REF:
      case LABEL_REF:
	// only use full register assignments
	if (GET_MODE_SIZE(dstMode).to_constant() != 4)
	  return false;
	/* these can be used directly. */
	*z = x;
	return true;

      case REG:
	{
	  rtx v = value[REGNO(x)];
	  unsigned v_usedRegs = usedRegs[REGNO(x)];
	  /* try to expand the register. */
	  if (v)
	    {
	      if (dstMode != GET_MODE(v) && (GET_CODE(v) != CONST_INT || v_usedRegs == (1 << FIRST_PSEUDO_REGISTER)))
		return false;

	      *z = v;
	      return true;
	    }

	  /* store the reg otherwise. */
	  if (GET_MODE(x) == dstMode)
	    *z = x;
	  else
	    *z = gen_rtx_REG (dstMode, REGNO(x));
	  return true;
	}
      case PLUS:
      case MINUS:
	// handle only in combination with const
	{
	  rtx y = XEXP(x, 0);
	  if (GET_CODE(y) != SYMBOL_REF && GET_CODE(y) == LABEL_REF && amiga_is_const_pic_ref (y))
	    return false;

	  if (GET_CODE(x) == PLUS) // create an own plus to be able to modify the constant offset (later).
	    *z = gen_rtx_PLUS(GET_MODE(x), y, XEXP(x, 1));
	  else
	    *z = gen_rtx_MINUS(GET_MODE(x), y, XEXP(x, 1));
	  return true;
	}

	/* memory reads. */
      case MEM:
	{
	  rtx m = XEXP(x, 0);
	  switch (GET_CODE(m))
	    {
	    case SYMBOL_REF:
	    case LABEL_REF:
	      /* these can be used directly. */
	      *z = x;
	      return true;

	    case REG:
	      if (!extend (&m, dstMode, m))
		return false;

	      *z = gen_rtx_MEM (GET_MODE(x), m);
	      return true;

	    case PLUS:
	    case MINUS:
	      // handle only in combination with const
	      {
		rtx y = XEXP(m, 0);
		if (!REG_P(y) && GET_CODE(y) != SYMBOL_REF && GET_CODE(y) == LABEL_REF && amiga_is_const_pic_ref (y))
		  return false;

		if (REG_P(y))
		  if (!extend (&y, dstMode, y))
		    return false;

		if (GET_CODE(x) == PLUS) // create an own plus to be able to modify the constant offset (later).
		  m = gen_rtx_PLUS(GET_MODE(m), y, XEXP(m, 1));
		else
		  m = gen_rtx_MINUS(GET_MODE(m), y, XEXP(m, 1));

		*z = gen_rtx_MEM (GET_MODE(x), m);
		return true;
	      }
	    default:
	      return false;
	    }
	  break;
	}
      default:
	return false;
      }
  }

public:
  track_var (track_var const * o = 0)
  {
    if (o)
      assign (o);
    else
      for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
	{
	  value[i] = 0;
	  usedRegs[i] = 0;
	  andMask[i] = 0xffffffff;
	}
  }

  int
  find_alias (rtx src)
  {
    rtx z = 0;
    if (extend (&z, GET_MODE(src), src))
      {
	for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
	  {
	    // do not alias small int value from -128 ... 127
	    if (rtx_equal_p (z, value[i]) && (GET_CODE(z) != CONST_INT || INTVAL(z) > 127 || INTVAL(z) < -128))
	      return i;
	  }
      }
    return -1;
  }
  void
  invalidate_mem (rtx dst)
  {
    rtx z = 0;
    if (extend (&z, GET_MODE(dst), dst))
      {
	for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
	  {
	    if (rtx_equal_p (z, value[i]))
	      {
		value[i] = 0;
		usedRegs[i] = 0;
		andMask[i] = 0xffffffff;
	      }
	  }
      }
  }

  rtx
  get (unsigned regno) const
  {
    if (regno >= FIRST_PSEUDO_REGISTER)
      return 0;

    return value[regno];
  }

  unsigned getMask(unsigned regno) const
  {
    if (regno >= FIRST_PSEUDO_REGISTER)
      return 0xffffffff;

    return andMask[regno];
  }

  void
  set (machine_mode mode, unsigned regno, rtx src, unsigned my_use, unsigned index)
  {
    if (regno >= FIRST_PSEUDO_REGISTER)
      return;

    if (mode == DImode && GET_CODE(src) == CONST_INT)
      {
	rtx hi = gen_rtx_CONST_INT(VOIDmode, INTVAL(src) >> 32);
	rtx lo = gen_rtx_CONST_INT(VOIDmode, INTVAL(src) & 0xffffffff);
	set(E_SImode, regno, hi, my_use, index);
	set(E_SImode, regno + 1, lo, my_use, index);
	return;
      }

    if (mode == E_SFmode && regno < 16)
      mode = E_SImode;

    for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (usedRegs[i] & (1 << regno))
	  {
	    value[i] = 0;
	    usedRegs[i] = 0;
	    andMask[i] = 0xffffffff;
	  }
      }

    if (extend (&value[regno], mode, src))
      {
	if (GET_CODE(src) == CONST_INT)
	  {
	    unsigned iv = UINTVAL(src);
	    setMask(regno, iv, mode);
	  }
	else if (REG_P(src) && REG_NREGS(src) == 1)
	    setMask(regno, andMask[REGNO(src)], mode);
	else
	  setMask(regno, 0xffffffff, mode);

	usedRegs[regno] = my_use;
	// convert reg value int regs value.
	if (REG_P(value[regno]))
	  {
	    unsigned refregno = REGNO(value[regno]);
	    rtx val = value[refregno];
	    if (!val)
	      {
		val = gen_rtx_CONST_INT(mode, 0x100000000000000LL | ((long long int ) (refregno) << 32) | (0xffffffff & -index));
		value[refregno] = val;
	      }
	    value[regno] = val;
	    usedRegs[regno] = usedRegs[refregno];
	  }
      }
    else
      {
	clear (mode, regno, index);
      }
  }

  /** set the mask and combine it with a previous mask if mode size < 4. */
  void
  setMask(unsigned regno, unsigned mask, machine_mode mode)
  {
    if (GET_MODE_SIZE(mode).to_constant() == 1)
      andMask[regno] = (andMask[regno] & 0xffffff00) | (mask & 0xff);
    else
    if (GET_MODE_SIZE(mode).to_constant() == 2)
      andMask[regno] = (andMask[regno] & 0xffff0000) | (mask & 0xffff);
    else
    andMask[regno] = mask;
  }

  bool
  equals (machine_mode dmode, unsigned regno, rtx x)
  {
    if (regno >= FIRST_PSEUDO_REGISTER)
      return false;

    if (x == 0 || value[regno] == 0)
      return false;

    machine_mode mode = GET_MODE(value[regno]);
    if (dmode == DImode && mode == VOIDmode && GET_CODE(x) == CONST_INT)
      {
	rtx hi = gen_rtx_CONST_INT(VOIDmode, INTVAL(x) >> 32);
	rtx lo = gen_rtx_CONST_INT(VOIDmode, INTVAL(x) & 0xffffffff);
	return equals(VOIDmode, regno, hi) && equals(VOIDmode, regno + 1, lo);
      }

    machine_mode xmode = GET_MODE(x);
    if (REG_P(x) && REGNO(x) < 16 && xmode == E_SFmode)
      xmode = E_SImode;

    if (mode == E_SFmode && regno < 16)
      mode = E_SImode;

    if (mode != xmode)
      return false;

    rtx z = 0;
    if (!extend (&z, GET_MODE(x), x))
      return false;

    return rtx_equal_p (z, value[regno]);
  }

  void
  clear (machine_mode mode, unsigned regno, unsigned index)
  {
    if (regno >= FIRST_PSEUDO_REGISTER)
      return;

    if (mode == E_SFmode && regno < 16)
      mode = E_SImode;
    value[regno] = gen_rtx_CONST_INT(mode, 0x100000000000000LL | ((long long int ) (regno) << 32) | index);
    usedRegs[regno] = 1 << FIRST_PSEUDO_REGISTER;
    setMask(regno, 0xffffffff, mode);
  }

  void
  clear_aftercall (unsigned index)
  {
    for (int i = 2; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (value[i] && MEM_P(value[i]))
	  {
	    value[i] = 0;
	    usedRegs[i] = 0;
	    andMask[i] = 0xffffffff;
	  }
      }
    clear (E_SImode, 0, index);
    clear (E_SImode, 1, index);
    clear (E_SImode, 8, index);
    clear (E_SImode, 9, index);
    clear (E_SImode, 16, index);
    clear (E_SImode, 17, index);
  }

  void
  clear_for_mask (unsigned def, unsigned index)
  {
    if (!def)
      return;
    for (int regno = 0; regno < FIRST_PSEUDO_REGISTER; ++regno)
      {
	// register changed or used somehow
	if ((1 << regno) & def)
	  clear (E_SImode, regno, index);
      }
  }

  void
  assign (track_var const * o)
  {
    for (int i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	value[i] = o->value[i];
	usedRegs[i] = o->usedRegs[i];
	andMask[i] = o->andMask[i];
      }
  }

  /* only keep common values in both sides. */
  void
  merge (track_var * o, unsigned)
  {
    for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (!rtx_equal_p (value[i], o->value[i]))
	  {
	    value[i] = o->value[i] = 0;
	    usedRegs[i] = 0;
	  }
	o->andMask[i] = andMask[i] |= o->andMask[i]; // or the masks
      }
  }

  /* true if a merge would not change anything.  */
  bool
  no_merge_needed (track_var const * o) const
  {
    for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (!rtx_equal_p (value[i], o->value[i]) || andMask[i] != (andMask[i] | o->andMask[i]))
	  return false;
      }
    return true;
  }
};

/* Information for each insn to detect alive registers. Enough for m68k.
 * Why a class? Maybe extend it for general usage.
 *
 * Track use & def separate to determine starting points.
 */
class insn_info
{
  rtx_insn * insn; // the insn

// usage flags
  unsigned myuse;  // bit set if registers are used in this statement
  unsigned hard; // bit set if registers can't be renamed
  unsigned use;  // bit set if registers are used in program flow
  unsigned def;  // bit set if registers are defined here

  enum proepis proepi;

  bool stack; // part of stack frame insns

// stuff to analyze insns
  bool label;
  bool jump;
  bool call;
  bool compare;
  bool dst_mem;
  bool src_mem;
  bool dst_plus;
  bool src_plus;
  rtx_code src_op;
  bool src_ee;
  bool src_2nd;
  bool src_const;

  machine_mode mode;

  rtx dst_reg;
  rtx dst_mem_reg;
  rtx dst_symbol;
  rtx src_reg;
  rtx src_mem_reg;
  rtx src_symbol;
  long int dst_mem_addr;
  long int src_intval;
  long int src_mem_addr;

  bool visited;

  int sp_offset;

  int dst_autoinc;
  int src_autoinc;

  unsigned multi_reg; /* bit field for register pairs. */

// values for all variables - if used
  track_var * track;

public:
  insn_info (rtx_insn * i = 0, enum proepis p = IN_CODE) :
      insn (i), myuse (0), hard (0), use (0), def (0), proepi (p), stack (false), label (false), jump (false), call (
	  false), compare (false), dst_mem (false), src_mem (false), dst_plus (false), src_plus (false), src_op (
	  (rtx_code) 0), src_ee (false), src_2nd (false), src_const (false), mode (VOIDmode), dst_reg (0), dst_mem_reg (
	  0), dst_symbol (0), src_reg (0), src_mem_reg (0), src_symbol (0), dst_mem_addr (0), src_intval (0), src_mem_addr (
	  0), visited (false), sp_offset (0), dst_autoinc (0), src_autoinc (0), multi_reg(0), track (0)
  {
  }

  unsigned
  get_multi_reg () const
  {
    return multi_reg;
  }

  track_var *
  get_track_var ();

  inline ptrdiff_t
  operator < (insn_info const & o) const
  {
    return this - &o;
  }

  int
  get_index () const;

  void
  plus_to_move (rtx_insn * newinsn);

  void
  swap_adds (rtx_insn * newinsn, insn_info & ii);

  void
  absolute2base (unsigned regno, unsigned base, rtx with_symbol);

  rtx
  make_absolute2base (unsigned regno, unsigned base, rtx with_symbol, bool apply);

  inline bool
  is_compare () const
  {
    return compare;
  }

  inline machine_mode
  get_mode () const
  {
    return mode;
  }

  inline bool
  is_dst_reg () const
  {
    return dst_reg;
  }

  inline bool
  is_dst_mem () const
  {
    return dst_mem;
  }

  inline bool
  is_src_mem () const
  {
    return src_mem;
  }

  inline bool
  is_src_mem_2nd () const
  {
    return src_2nd && src_mem;
  }

  inline bool
  has_dst_memreg () const
  {
    return dst_mem_reg;
  }

  inline bool
  has_src_memreg () const
  {
    return src_mem_reg;
  }

  inline rtx
  get_dst_symbol () const
  {
    return dst_symbol;
  }

  inline rtx
  get_src_symbol () const
  {
    return src_symbol;
  }
  inline bool
  has_dst_addr () const
  {
    return dst_mem_addr;
  }

  inline bool
  has_src_addr () const
  {
    return src_mem_addr;
  }

  inline bool
  is_label () const
  {
    return label;
  }

  inline bool
  is_jump () const
  {
    return jump;
  }

  inline bool
  is_call () const
  {
    return call;
  }

  inline long
  get_dst_mem_addr () const
  {
    return dst_mem_addr;
  }

  inline long
  get_src_mem_addr () const
  {
    return src_mem_addr;
  }

  inline bool
  is_src_reg () const
  {
    return src_reg && !src_op;
  }

  inline int
  get_src_op () const
  {
    return src_op;
  }

  inline bool
  is_src_ee () const
  {
    return src_ee;
  }

  inline bool
  is_src_mem_plus () const
  {
    return src_mem && src_plus;
  }

  inline bool
  is_dst_mem_plus () const
  {
    return dst_mem && dst_plus;
  }

  inline int
  get_dst_regno () const
  {
    return dst_reg ? REGNO(dst_reg) : -1;
  }

  inline int
  get_src_regno () const
  {
    return src_reg ? REGNO(src_reg) : -1;
  }

  inline rtx
  get_src_reg () const
  {
    return src_reg;
  }

  inline rtx
  get_dst_reg () const
  {
    return dst_reg;
  }

  inline int
  get_src_mem_regno () const
  {
    return src_mem_reg ? REGNO(src_mem_reg) : -1;
  }

  inline int
  get_dst_mem_regno () const
  {
    return dst_mem_reg ? REGNO(dst_mem_reg) : -1;
  }

  inline rtx
  get_src_mem_reg () const
  {
    return src_mem_reg;
  }

  inline rtx
  get_dst_mem_reg () const
  {
    return dst_mem_reg;
  }

  inline int
  get_src_intval () const
  {
    return src_intval;
  }

  inline int
  get_dst_intval () const
  {
    return dst_mem_addr;
  }

  inline bool
  is_src_const () const
  {
    return src_const;
  }

  inline void
  mark_jump ()
  {
    jump = true;
  }
  inline void
  mark_call ()
  {
    call = true;
  }
  inline void
  mark_label ()
  {
    label = true;
  }

  void
  fledder (rtx set);

  void
  fledder_src_mem (rtx src);

  /* update usage. */
  void
  update (insn_info & o)
  {
    myuse = o.myuse;
    hard = o.hard;
    use = o.use;
    def = o.def;
    multi_reg = o.multi_reg;
  }

  inline rtx_insn *
  get_insn () const
  {
    return insn;
  }

  void
  mark_stack ()
  {
    stack = true;
  }

  bool
  is_stack () const
  {
    return stack;
  }

  inline enum proepis
  in_proepi () const
  {
    return proepi;
  }

  inline void
  set_proepi (enum proepis p)
  {
    proepi = p;
  }

  inline void
  reset_flags ()
  {
    label = false;
    jump = false;
    compare = false;
    dst_mem = false;
    src_mem = false;
    dst_plus = false;
    src_plus = false;
    src_op = (rtx_code) 0;
    src_ee = false;
    src_const = false;

    mode = VOIDmode;

    dst_reg = 0;
    dst_mem_reg = 0;
    dst_symbol = 0;
    src_reg = 0;
    src_mem_reg = 0;
    src_symbol = 0;
    dst_mem_addr = 0;

    src_intval = 0;
    src_mem_addr = 0;

    dst_autoinc = 0;
    src_autoinc = 0;
  }

  inline int
  get_src_autoinc () const
  {
    return src_autoinc;
  }

  inline int
  get_dst_autoinc () const
  {
    return dst_autoinc;
  }

  inline bool
  is_empty ()
  {
    return !def && !use && !hard;
  }

  inline void
  mark_myuse (int regno)
  {
    myuse |= 1 << regno;
    use |= 1 << regno;
  }

  inline void
  mark_use (int regno)
  {
    use |= 1 << regno;
  }

  inline void
  mark_def (int regno)
  {
    def |= 1 << regno;
  }

  inline void
  mark_hard (int regno)
  {
    hard |= 1 << regno;
  }

  inline void
  unset (int regno)
  {
    use &= ~(1 << regno);
    def &= ~(1 << regno);
    hard &= ~(1 << regno);
  }

  inline unsigned
  get_use () const
  {
    return use;
  }

  inline void
  set_use (unsigned u)
  {
    use = u;
  }

  inline unsigned
  get_myuse () const
  {
    return myuse;
  }

  inline void
  set_myuse (unsigned u)
  {
    myuse = u;
  }

  inline unsigned
  get_def () const
  {
    return def;
  }

  inline void
  set_def(unsigned u)
  {
    def = u;
  }

  inline unsigned
  get_hard () const
  {
    return hard;
  }

  inline bool
  is_use (int regno)
  {
    return (use & (1 << regno)) != 0;
  }

  inline bool
  is_myuse (int regno)
  {
    return (myuse & (1 << regno)) != 0;
  }

  inline bool
  is_def (int regno)
  {
    return (def & (1 << regno)) != 0;
  }

  inline bool
  is_hard (int regno)
  {
    return (hard & (1 << regno)) != 0;
  }

  inline void
  clear_hard_def ()
  {
    hard = 0;
    def = 0;
  }

  /*
   * update for previous insn.
   * - remove regs which are defined here
   * - add regs which are used here
   * - reset _def
   * - restrain _hard to used
   */
  inline void
  updateWith (insn_info const & o)
  {
    use &= ~o.def;
    use |= o.use;
    def = 0;
  }

  inline insn_info &
  merge (insn_info const & o)
  {
    myuse = o.myuse;
    use = (use & ~o.def) | o.use;
    def |= o.def;
    hard |= o.hard;
    multi_reg = o.multi_reg;
    return *this;
  }

  inline insn_info &
  or_def (insn_info const & o)
  {
    def |= o.def;
    return *this;
  }

  inline insn_info &
  drop_def ()
  {
    use &= ~def;
    return *this;
  }

  inline insn_info &
  make_hard ()
  {
    hard = use | def;
    return *this;
  }

  inline insn_info &
  make_clobber ()
  {
    hard = use = def = use | def;
    return *this;
  }

  inline bool
  contains (insn_info const & o) const
  {
    if (o.def & ~def)
      return false;
    if (o.use & ~use)
      return false;
    if (o.hard & ~hard)
      return false;
    return true;
  }

  inline int
  get_sp_offset () const
  {
    return sp_offset;
  }

  inline void
  set_sp_offset (int sp)
  {
    sp_offset = sp;
  }

  inline bool
  is_visited () const
  {
    return visited;
  }

  inline void
  mark_visited ()
  {
    visited = true;
  }

  inline void
  clear_visited ()
  {
    visited = false;
  }

  void
  scan ();

  void
  scan_rtx (rtx);

  bool
  make_post_inc (int regno);

  void
  auto_inc_fixup (int regno, int size);

  /* return bits for alternate free registers. */
  unsigned
  get_free_mask () const
  {
    if (def & hard)
      return 0;

    if (!def)
      return 0;

    unsigned def_no_cc = def & ~(1 << FIRST_PSEUDO_REGISTER);
    if (def_no_cc > 0x4000)
      return 0;

    unsigned mask = def_no_cc - 1;
    /* more than one register -> don't touch. */
    if ((mask & ~def) != mask)
      return 0;

    if (def_no_cc > 0xff)
      mask &= 0xff00;

    return mask & ~use;
  }

  unsigned
  get_regbit () const
  {
    if (GET_MODE_SIZE(mode).to_constant() > 4)
      return 0;
    return def & ~hard & ~use & 0x7fff;
  }

  void
  set_insn (rtx_insn * newinsn);

  void
  a5_to_a7 (rtx a7, int add);
};

bool
insn_info::make_post_inc (int regno)
{
  rtx pattern = PATTERN (insn);
  rtx_insn * new_insn = make_insn_raw (pattern);

  // convert into POST_INC
  rtx set0 = single_set (new_insn);
  if (!set0)
    return false;

  rtx set = set0;

  if (is_compare ())
    set = SET_SRC(set);
  rtx mem = get_dst_mem_regno () == regno ? SET_DEST(set) : SET_SRC(set);

  if (src_op && get_src_mem_regno () == regno)
    {
      if (src_op == NEG || src_op == NOT || (src_op >= SIGN_EXTEND && src_op <= PARITY)
    		  || src_op == SS_NEG || src_op == US_NEG || src_op == SS_ABS
			  || src_op == SS_TRUNCATE || src_op == US_TRUNCATE)
	mem = XEXP(mem, 0);
      else
	mem = XEXP(mem, 1);
    }

  rtx reg = XEXP(mem, 0);

  XEXP(mem, 0) = gen_rtx_POST_INC(E_SImode, reg);

  if (insn_invalid_p (new_insn, 0))
    {
      XEXP(mem, 0) = reg;
      insn_invalid_p (insn, 0);
      return 0;
    }

  SET_INSN_DELETED(insn);
  (get_dst_mem_regno () == regno ? dst_autoinc : src_autoinc) = GET_MODE_SIZE(mode).to_constant();
  insn = emit_insn_after (PATTERN (new_insn), insn);
  insn_invalid_p (insn, 0);

  return 1;
}

static rtx
add_clobbers (rtx_insn * oldinsn)
{
  rtx pattern = PATTERN (oldinsn);
  if (GET_CODE(pattern) != PARALLEL)
    return pattern;

  int num_clobbers = 0;
  for (int j = XVECLEN (pattern, 0) - 1; j >= 0; j--)
    {
      rtx x = XVECEXP(pattern, 0, j);
      if (GET_CODE(x) == CLOBBER)
	++num_clobbers;
    }

  if (!num_clobbers)
    return pattern;

  rtx newpat = gen_rtx_PARALLEL(VOIDmode, rtvec_alloc (num_clobbers + 1));
  for (int j = XVECLEN (pattern, 0) - 1; j >= 0; j--)
    {
      rtx x = XVECEXP(pattern, 0, j);
      if (GET_CODE(x) == CLOBBER)
	XVECEXP(newpat, 0, num_clobbers--) = x;
    }

  XVECEXP(newpat, 0, 0) = XVECEXP(pattern, 0, 0);
  return newpat;
}

void
insn_info::auto_inc_fixup (int regno, int size)
{
//  debug_rtx (insn);
  rtx set0 = single_set (insn);
  rtx set = set0;
  if (is_compare ())
    set = SET_SRC(set);

  // add to register
  if (get_src_regno () == regno)
    {
      rtx src = SET_SRC(set);
      if (get_src_intval () == size)
	{
	  src_intval = 0;
	  src_plus = false;
	  SET_SRC(set) = XEXP(src, 0);
	}
      else
	XEXP(src, 1) = gen_rtx_CONST_INT (VOIDmode, src_intval -= size);
    }
  else if (get_src_mem_regno () == regno)
    {
      // src mem used ?
      rtx mem = SET_SRC(set);
      if (src_op)
	{
	  if (MEM_P(XEXP(mem, 0)))
	    mem = XEXP(mem, 0);
	  else
	    mem = XEXP(mem, 1);
	}
      rtx plus = XEXP(mem, 0);

      if (src_mem_addr == size)
	{
	  XEXP(mem, 0) = XEXP(plus, 0);
	  src_mem_addr = 0;
	  src_plus = false;
	}
      else
	XEXP(plus, 1) = gen_rtx_CONST_INT (VOIDmode, src_mem_addr -= size);
    }

  if (get_dst_mem_regno () == regno)
    {
      rtx mem = SET_DEST(set);
      rtx plus = XEXP(mem, 0);
      if (dst_mem_addr == size)
	{
	  XEXP(mem, 0) = XEXP(plus, 0);
	  dst_mem_addr = 0;
	  dst_plus = false;
	}
      else
	XEXP(plus, 1) = gen_rtx_CONST_INT (VOIDmode, dst_mem_addr -= size);
    }

  rtx pattern = add_clobbers (insn);

  SET_INSN_DELETED(insn);
  insn = emit_insn_after (pattern, insn);
}

track_var *
insn_info::get_track_var ()
{
  if (!track)
    track = new track_var ();
  return track;
}

void
insn_info::scan ()
{
  rtx pattern = PATTERN (insn);
  if (ANY_RETURN_P(pattern))
    {
      tree type = TYPE_SIZE(TREE_TYPE (DECL_RESULT (current_function_decl)));
      int sz = type ? TREE_INT_CST_LOW(type) : 0;
      // log ("return size %d\n", sz);
      if (sz && sz <= 64)
	{
	  mark_hard (0);
	  mark_myuse (0);
	  if (sz > 32)
	    {
	      mark_hard (1);
	      mark_myuse (1);
	    }
	}
    }
  else if (CALL_P(insn))
    {
      /* add mregparm registers. */
      for (rtx link = CALL_INSN_FUNCTION_USAGE(insn); link; link = XEXP(link, 1))
	{
	  rtx op, reg;

	  if (GET_CODE (op = XEXP (link, 0)) == USE && REG_P(reg = XEXP (op, 0)))
	    for (unsigned r = REGNO(reg); r < END_REGNO (reg); ++r)
	      mark_myuse (r);
	}
      /* mark stack pointer used. there could be parameters on stack*/
      mark_myuse (15);
      /* mark scratch registers. */
      mark_def (0);
      mark_def (1);
      mark_def (8);
      mark_def (9);
      mark_def (16);
      mark_def (17);
      /* also mark all registers as not renamable */
      hard = use;
    }
  scan_rtx (pattern);
}

/* scan rtx for registers and set the corresponding flags. */
void
insn_info::scan_rtx (rtx x)
{
  if (REG_P(x))
    {
      int n0 = REG_NREGS(x);
      for (int n = n0, r = REGNO(x); n > 0; --n, ++r)
	{
	  mark_myuse (r);
	  if (n0 > 1)
	    multi_reg |= 1<<r;
	}
      return;
    }

  if (x == cc0_rtx)
    {
      mark_myuse (FIRST_PSEUDO_REGISTER);
      return;
    }

  RTX_CODE code = GET_CODE(x);

  /* handle SET and record use and def. */
  if (code == SET)
    {
      unsigned u = use;
      unsigned mu = myuse;
      use = myuse = 0;
      rtx dst = SET_DEST(x);
      scan_rtx (dst);
      if (REG_P(dst) || ((GET_CODE(dst) == STRICT_LOW_PART || GET_CODE(dst) == SUBREG) && REG_P(XEXP(dst, 0))))
	{
	  def |= use;
	  if ((GET_CODE(dst) == STRICT_LOW_PART || GET_CODE(dst) == SUBREG))
	    use |= u;
	  else
	    use = u;
	  myuse = mu;
	}

      // avoid side effects from myuse -> def, e.g. adding the dst reg to def by src auto inc
      mu = myuse;
      myuse = 0;
      scan_rtx (SET_SRC(x));
      myuse |= mu;

      int code = GET_CODE(SET_SRC(x));
      if (code == ASM_OPERANDS)
	hard |= def | use;
      return;
    }

  if (code == TRAP_IF)
    {
      /* mark all registers used. */
      hard = use = myuse = (1 << FIRST_PSEUDO_REGISTER) - 1;
      return;
    }

  const char *fmt = GET_RTX_FORMAT(code);
  for (int i = GET_RTX_LENGTH (code) - 1; i >= 0; i--)
    {
      if (fmt[i] == 'e')
	scan_rtx (XEXP(x, i));
      else if (fmt[i] == 'E')
	for (int j = XVECLEN (x, i) - 1; j >= 0; j--)
	  {
	    unsigned u = use;
	    unsigned mu = myuse;
	    unsigned d = def;
	    unsigned mr = multi_reg;
	    scan_rtx (XVECEXP(x, i, j));
	    use |= u;
	    myuse |= mu;
	    def |= d;
	    multi_reg |= mr;
	    if ((def - 1) & def)
	      multi_reg |= def;
	  }
    }

  if (code == POST_INC || code == PRE_DEC || code == CLOBBER)
    def |= myuse;
  if (code == CLOBBER)
    multi_reg |= def;
}

void
insn_info::fledder_src_mem (rtx src)
{
  src_mem = true;
  rtx mem = XEXP(src, 0);

  if (GET_CODE(mem) == POST_INC)
    src_autoinc = 1, mem = XEXP(mem, 0);
  else if (GET_CODE(mem) == PRE_DEC)
    src_autoinc = -1, mem = XEXP(mem, 0);

  if (REG_P(mem))
    src_mem_reg = mem;
  else if (GET_CODE(mem) == CONST_INT)
    src_mem_addr = INTVAL(mem);
  else if (GET_CODE(mem) == SYMBOL_REF)
    src_symbol = mem;
  else if (GET_CODE(mem) == PLUS)
    {
      src_plus = true;
      rtx reg = XEXP(mem, 0);
      rtx konst = XEXP(mem, 1);
      if (REG_P(reg) && GET_CODE(konst) == CONST_INT)
	{
	  src_mem_reg = reg;
	  src_const = true;
	  src_mem_addr = INTVAL(konst);
	}
    }
  else if (GET_CODE(mem) == CONST)
    {
      mem = XEXP(mem, 0);
      if (GET_CODE(mem) == PLUS)
	{
	  rtx sym = XEXP(mem, 0);
	  if (GET_CODE(sym) == SYMBOL_REF)
	    {
	      src_plus = true;
	      src_symbol = sym;
	      src_mem_addr = INTVAL(XEXP(mem, 1));
	    }
	}
    }
}

/* read the set and grab infos */
void
insn_info::fledder (rtx set)
{
  if (!set || GET_CODE(set) == PARALLEL)
    return;

  rtx dst = SET_DEST(set);
  rtx src = SET_SRC(set);

  if (dst == cc0_rtx)
    {
      compare = true;
      set = src;
      dst = SET_DEST(set);
      src = SET_SRC(set);
    }

  if (GET_CODE(dst) == STRICT_LOW_PART || GET_CODE(dst) == SUBREG)
    dst = XEXP(dst, 0);

  mode = GET_MODE(dst);
  if (mode == VOIDmode)
    mode = GET_MODE(src);

  if (REG_P(dst))
    {
      dst_reg = dst;
    }
  else if (MEM_P(dst))
    {
      dst_mem = true;
      rtx mem = XEXP(dst, 0);

      if (GET_CODE(mem) == POST_INC)
	dst_autoinc = 1, mem = XEXP(mem, 0);
      else if (GET_CODE(mem) == PRE_DEC)
	dst_autoinc = -1, mem = XEXP(mem, 0);

      if (REG_P(mem))
	dst_mem_reg = mem;
      else if (GET_CODE(mem) == CONST_INT)
	dst_mem_addr = INTVAL(mem);
      else if (GET_CODE(mem) == SYMBOL_REF)
	dst_symbol = mem;
      else if (GET_CODE(mem) == PLUS)
	{
	  dst_plus = true;
	  rtx reg = XEXP(mem, 0);
	  rtx konst = XEXP(mem, 1);
	  if (REG_P(reg) && GET_CODE(konst) == CONST_INT)
	    {
	      dst_mem_reg = reg;
	      dst_mem_addr = INTVAL(konst);
	    }
	}
      else if (GET_CODE(mem) == CONST)
	{
	  mem = XEXP(mem, 0);
	  if (GET_CODE(mem) == PLUS)
	    {
	      rtx sym = XEXP(mem, 0);
	      if (GET_CODE(sym) == SYMBOL_REF)
		{
		  dst_plus = true;
		  dst_symbol = sym;
		  dst_mem_addr = INTVAL(XEXP(mem, 1));
		}
	    }
	}
    }

  /* It' some kind of operation, e.g. PLUS, XOR, NEG, ... */
  rtx alt_src_reg = 0;
  int code = GET_CODE(src);
  if (!REG_P(src) && !MEM_P(src) && code != CONST_INT && code != CONST && code != CONST_WIDE_INT && code != CONST_DOUBLE
      && code != CONST_FIXED && code != CONST_STRING)
    {
      src_op = GET_CODE(src);
      const char *fmt = GET_RTX_FORMAT(code);
      if (fmt[0] == 'e' && fmt[1] == 'e')
	{
	  src_ee = true;
	  rtx operand = XEXP(src, 1);
	  if (GET_CODE(operand) == CONST_INT || GET_CODE(operand) == CONST_WIDE_INT)
	    src_const = true, src_intval = INTVAL(operand);
	  else if (REG_P(operand))
	    {
	      alt_src_reg = operand;
	    }
	  else if (MEM_P(operand))
	    {
	      // it' something like reg = op(reg, mem(...))
	      src_2nd = true;
	      fledder_src_mem (operand);
	    }
	}
      src = XEXP(src, 0);
    }

  if (REG_P(src))
    {
      src_reg = src;
    }
  else if (MEM_P(src))
    {
      fledder_src_mem (src);
    }
  else if (GET_CODE(src) == CONST_INT)
    {
      src_const = true;
      src_intval = INTVAL(src);
    }
  if (alt_src_reg)
    src_reg = alt_src_reg;
}

/* create a copy for a reg. Optional specify a new register number. */
static rtx
copy_reg (rtx reg, int newregno)
{
  if (newregno < 0)
    newregno = REGNO(reg);
  rtx x = gen_raw_REG (GET_MODE(reg), newregno);
  x->jump = reg->jump;
  x->call = reg->call;
  x->unchanging = reg->unchanging;
  x->volatil = reg->volatil;
  x->in_struct = reg->in_struct;
  x->used = reg->used;
  x->frame_related = reg->frame_related;
  x->return_val = reg->return_val;

  x->u.reg.attrs = reg->u.reg.attrs;
  return x;
}

/* Rename the register plus track all locs to undo these changes. */
static void
find_reg_modes_by_no (rtx x, unsigned oldregno,std::set<machine_mode> & modes)
{
  if (!x)
    return;

  RTX_CODE code = GET_CODE(x);

  const char *fmt = GET_RTX_FORMAT(code);
  for (int i = GET_RTX_LENGTH (code) - 1; i >= 0; i--)
    {
      if (fmt[i] == 'e')
	{
	  rtx y = XEXP(x, i);
	  if (REG_P(y))
	    {
	      if (REGNO(y) == oldregno)
		modes.insert(GET_MODE(y));
	    }
	  else
	    find_reg_modes_by_no (y, oldregno, modes);
	}
      else if (fmt[i] == 'E')
	for (int j = XVECLEN (x, i) - 1; j >= 0; j--)
	  {
	    rtx z = XVECEXP(x, i, j);
	    find_reg_modes_by_no (z, oldregno, modes);
	  }
    }
}

/*
 * Collect some data.
 */
static std::vector<insn_info> infos;
typedef std::vector<insn_info>::iterator insn_info_iterator;

// insn->u2.insn_uid -> rtx_insn *
static std::multimap<int, rtx_insn *> label2jump;
typedef std::multimap<int, rtx_insn *>::iterator l2j_iterator;

// index -> index
static std::multimap<unsigned, unsigned> jump2label;
typedef std::multimap<unsigned, unsigned>::iterator j2l_iterator;

static std::map<rtx_insn *, insn_info *> insn2info;
typedef std::map<rtx_insn *, insn_info *>::iterator i2i_iterator;

static std::set<unsigned> scan_starts;
typedef std::set<unsigned>::iterator su_iterator;

static insn_info * info0;
static unsigned usable_regs;

// registers used during rename
static std::vector<rtx> dstregs;

static void
update_insn2index ()
{
  infos.reserve (infos.size () * 8 / 7 + 2);
  insn2info.clear ();
  /* needs a separate pass since the insn_infos require fixed addresses for ->get_index() */
  for (unsigned i = 0; i < infos.size (); ++i)
    {
      insn_info & ii = infos[i];
      insn2info.insert (std::make_pair (ii.get_insn (), &ii));
    }
  info0 = &infos[0];
}

static void
update_label2jump ()
{
  update_insn2index ();
  jump2label.clear();

  for (unsigned index = 0; index < infos.size (); ++index)
    {
      insn_info & ii = infos[index];
      if (ii.is_label ())
	for (l2j_iterator i = label2jump.find (ii.get_insn ()->u2.insn_uid), k = i;
	    i != label2jump.end () && i->first == k->first; ++i)
	  jump2label.insert (std::make_pair (insn2info.find (i->second)->second->get_index (), index));
    }
}

int
insn_info::get_index () const
{
  insn_info * ii = &infos[0];

  if (ii == info0)
    {
      ptrdiff_t diff = ((char const *) this - (char const *) ii);
      unsigned pos = diff / sizeof(insn_info);
      if (pos < infos.size ())
	return pos;
    }

// realloc happened...
  for (unsigned i = 0; i < infos.size (); ++i)
    if (infos[i].get_insn () == this->insn)
      return i;

// whoops!?
  return 0;
}

void
insn_info::plus_to_move (rtx_insn * newinsn)
{
  insn = newinsn;
  src_op = (rtx_code) 0;
  src_reg = XEXP(PATTERN (newinsn), 1);
  insn2info.insert (std::make_pair (insn, this));
// usage flags did not change
}

void
insn_info::swap_adds (rtx_insn * newinsn, insn_info & ii)
{
  insn = newinsn;

  std::swap (*this, ii);

  insn2info.insert (std::make_pair (insn, this));
  insn2info.insert (std::make_pair (ii.insn, &ii));

// usage flags did not change
}

static
void
replace_reg (rtx x, unsigned regno, rtx newreg, int offset)
{
  RTX_CODE code = GET_CODE(x);
  const char *fmt = GET_RTX_FORMAT(code);
  for (int i = GET_RTX_LENGTH (code) - 1; i >= 0; i--)
    {
      if (fmt[i] == 'e')
	{
	  rtx y = XEXP(x, i);
	  if (REG_P(y) && REGNO(y) == regno)
	    {
	      XEXP(x, i) = newreg;
	      if (offset && i + 1 < GET_RTX_LENGTH(code))
		{
		  rtx c = XEXP(x, i + 1);
		  if (GET_CODE(c) == CONST_INT)
		    XEXP(x, i + 1) = gen_rtx_CONST_INT (GET_MODE(x), INTVAL(c) + offset);
		}
	    }
	  else
	    replace_reg (y, regno, newreg, offset);
	}
      else if (fmt[i] == 'E')
	for (int j = XVECLEN (x, i) - 1; j >= 0; j--)
	  replace_reg (XVECEXP(x, i, j), regno, newreg, offset);
    }
}

void
insn_info::a5_to_a7 (rtx a7, int add)
{
  if (proepi == IN_EPILOGUE && src_mem_reg && get_src_mem_regno () == FRAME_POINTER_REGNUM)
    {
      rtx set = single_set (insn);
      if (set)
	{
	  SET_SRC(set) = gen_rtx_MEM (mode, gen_rtx_POST_INC(E_SImode, a7));
	  return;
	}
    }
  replace_reg (PATTERN (insn), FRAME_POINTER_REGNUM, a7, add-4);
}

void
insn_info::set_insn (rtx_insn * newinsn)
{
  insn = newinsn;

  reset_flags ();

  fledder (single_set (insn));
}

rtx
insn_info::make_absolute2base (unsigned regno, unsigned base, rtx with_symbol, bool apply)
{
  rtx set = single_set (get_insn ());
  rtx src = SET_SRC(set);
  rtx dst = SET_DEST(set);
  rtx reg = gen_raw_REG (E_SImode, regno);
  bool vola = src->volatil;

  if (is_dst_mem () && (has_dst_addr () || get_dst_symbol ()) && !has_dst_memreg () && get_dst_symbol () == with_symbol)
    {
      unsigned addr = get_dst_mem_addr ();
      unsigned offset = addr - base;
      if (offset <= 0x7ffe)
	{
	  if (base == addr)
	    dst = gen_rtx_MEM (mode, reg);
	  else
	    dst = gen_rtx_MEM (mode, gen_rtx_PLUS(E_SImode, reg, gen_rtx_CONST_INT (E_SImode, offset)));

	  if (apply)
	    {
	      dst_mem_reg = reg;
	      dst_mem = true;
	      dst_mem_addr = offset;
	      dst_plus = offset != 0;
	    }
	}
    }

  if (is_src_mem () && (has_src_addr () || get_src_symbol ()) && !has_src_memreg () && get_src_symbol () == with_symbol)
    {
      unsigned addr = get_src_mem_addr ();
      unsigned offset = addr - base;
      if (offset <= 0x7ffe)
	{
	  if (base == addr)
	    src = gen_rtx_MEM (mode, reg);
	  else
	    src = gen_rtx_MEM (mode, gen_rtx_PLUS(E_SImode, reg, gen_rtx_CONST_INT (E_SImode, offset)));

	  /* some operation to the same value as dst. eg. eor #5,symbol+8 -> eor #5,8(ax) */
	  if (src_op)
	    {
	      rtx srccopy = copy_rtx(SET_SRC(set));
	      // find the parent of the MEM
	      rtx outer = srccopy;
	      while (!MEM_P(XEXP(outer, 0)))
		outer = XEXP(outer, 0);

	      XEXP(outer, 0) = src;
	      src = srccopy;
	    }

	  if (apply)
	    {
	      src_mem_reg = reg;
	      src_mem = true;
	      src_mem_addr = offset;
	      src_plus = offset != 0;
	    }
	}
    }

  rtx pattern = gen_rtx_SET(dst, src);
  src->volatil = vola;

  return pattern;
}

void
insn_info::absolute2base (unsigned regno, unsigned base, rtx with_symbol)
{
  rtx pattern = make_absolute2base (regno, base, with_symbol, true);

  SET_INSN_DELETED(insn);
  insn = emit_insn_after (pattern, insn);

  mark_myuse (regno);

  insn2info.insert (std::make_pair (insn, this));
}
/*
 * Reset collected data.
 */
static void
clear (void)
{
  label2jump.clear ();
  jump2label.clear ();
  insn2info.clear ();
  infos.clear ();
  scan_starts.clear ();
}

/*
 *  return true if the register is DEAD.
 *  Do not check at jumps.
 */
static bool
is_reg_dead (unsigned regno, unsigned _pos)
{
// skip labels.
  for (unsigned pos = _pos + 1; pos < infos.size (); ++pos)
    {
      insn_info & ii = infos[pos];
      // skip entries without info
      if (ii.is_empty ())
	continue;

      // not dead if usage is reported in the next statement
      return !ii.is_use (regno) && !ii.is_hard (regno);
    }
  return true;
}

bool dump_cycles;
bool dump_reg_track;
void
append_reg_cache (FILE * f, rtx_insn * insn)
{
  i2i_iterator i = insn2info.find (insn);
  if (i == insn2info.end ())
    return;

  insn_info & jj = *i->second;
  unsigned index = jj.get_index ();
  if (index + 1 < infos.size ())
    ++index;
  insn_info & ii = infos[index];

  track_var * track = ii.get_track_var ();
  if (track == 0)
    return;

  fprintf (f, "\n");

  for (int regno = 0; regno < FIRST_PSEUDO_REGISTER; ++regno)
    {
      rtx v = track->get (regno);
      unsigned mask = track->getMask(regno);
      if (!v && mask == 0xffffffff)
	continue;

//      if (GET_CODE(v) == CONST_INT && GET_MODE(v) == VOIDmode)
//	continue;

      fprintf (f, "%s=", reg_names[regno]);

      if (v)
	print_inline_rtx (f, v, 12);
      else
	fprintf(f, "---");

      fprintf (f, "%08x\n", mask);
    }
}

/* helper stuff to enhance the asm output. */
void
append_reg_usage (FILE * f, rtx_insn * insn)
{
  i2i_iterator i = insn2info.find (insn);
  if (i == insn2info.end ())
    return;

  insn_info & ii = *i->second;

  if (f != stderr)
    {
      int cost = -1;
      rtx set = single_set(ii.get_insn());
      if (set)
	cost = rtx_cost(set, GET_MODE(SET_DEST(set)), INSN, 0, true);
      if (be_very_verbose)
	fprintf (f, "\n\t\t\t\t#%d\t%d %d\t", ii.get_index (), cost, set ? pattern_cost(set, true): 0);
      else
	{
	  fprintf (f, "\t# %d %d", cost, set ? pattern_cost(set, true): 0);
	  return;
	}
    }

  fprintf (f, "%c ", ii.in_proepi () == IN_PROLOGUE ? 'p' : ii.in_proepi () >= IN_EPILOGUE ? 'e' : ' ');

  for (int j = 0; j < 8; ++j)
    if (ii.is_use (j) || ii.is_def (j))
      {
	fprintf (f, ii.is_hard (j) ? "!" : " ");
	fprintf (f, ii.is_def (j) ? ii.is_use (j) ? "*" : "+" : ii.is_myuse (j) ? "." : " ");
	fprintf (f, "d%d ", j);
      }
    else
      fprintf (f, "     ");

  for (int j = 8; j < 16; ++j)
    if (ii.is_use (j) || ii.is_def (j))
      {
	fprintf (f, ii.is_hard (j) ? "!" : " ");
	fprintf (f, ii.is_def (j) ? ii.is_use (j) ? "*" : "+" : ii.is_myuse (j) ? "." : " ");
	fprintf (f, "a%d ", j - 8);
      }
    else
      fprintf (f, "     ");

  if (ii.is_use (FIRST_PSEUDO_REGISTER))
    fprintf (f, ii.is_def (FIRST_PSEUDO_REGISTER) ? "+cc " : " cc ");
  else
    fprintf (f, "    ");

  // append fp usage info if present
  if ((ii.get_use () | ii.get_def ()) & ~0xffff)
    {
      for (int j = 16; j < 24; ++j)
	if (ii.is_use (j) || ii.is_def (j))
	  {
	    fprintf (f, ii.is_hard (j) ? "!" : " ");
	    fprintf (f, ii.is_def (j) ? ii.is_use (j) ? "*" : "+" : ii.is_myuse (j) ? "." : " ");
	    fprintf (f, "f%d ", j - 16);
	  }
	else
	  fprintf (f, "     ");
    }

  if (f == stderr)
    fprintf (f, "\n");

}

/*
 * Helper function to dump the code.
 * Sometimes used during debugging.
 */
static void
dump_insns (char const * name, bool all)
{
  fprintf (stderr, "====================================: %s\n", name);
  if (all)
    {
      for (rtx_insn * insn = get_insns (); insn && insn != infos[0].get_insn (); insn = NEXT_INSN (insn))
	debug_rtx (insn);
    }
  for (unsigned i = 0; i < infos.size (); ++i)
    {
      fprintf (stderr, "%d: ", i);

      rtx_insn * insn = infos[i].get_insn ();
      if (i < infos.size ())
	append_reg_usage (stderr, insn);

      fprintf (stderr, "\t");
      debug_rtx (insn);

      if (all)
	{
	  rtx_insn * p = i + 1 < infos.size () ? infos[i + 1].get_insn () : 0;
	  for (rtx_insn * q = NEXT_INSN (insn); q && q != p; q = NEXT_INSN (q))
	    debug_rtx (q);
	}
    }
}

/* This is the important function to track register usage plus hard/live state.
 *
 * Start at bottom and work upwards. On all labels trigger all jumps referring to this label.
 * A set destination into a register is a def. All other register references are an use.
 * Hard registers cann't be renamed and are mandatory for regparms and asm_operands.
 */
static void
update_insn_infos (void)
{
  /* add all return (jump outs) and start analysis there. */
  std::set<unsigned> & todo = scan_starts;

  if (todo.begin () == todo.end ())
    todo.insert (infos.size () - 1);

  bool locka4 = flag_pic >= 3;

  while (!todo.empty ())
    {
      int start = *todo.begin ();
      todo.erase (todo.begin ());
      insn_info ii = infos[start];

      enum proepis proepi = ii.in_proepi ();

      // mark sp reg as used.
      if (proepi >= IN_EPILOGUE)
	ii.mark_use (STACK_POINTER_REGNUM), infos[start].mark_use (STACK_POINTER_REGNUM);

      for (int pos = start; pos >= 0; --pos)
	{
	  insn_info & pp = infos[pos];
	  rtx_insn * insn = pp.get_insn ();

	  // do not run into previous epilogue
	  if (pp.in_proepi () >= IN_EPILOGUE && !proepi)
	    break;

	  proepi = pp.in_proepi ();

	  /* no new information -> break. */
	  if (pos != start && pp.is_visited () && !JUMP_P(insn) && pp.contains (ii))
	    break;

	  ii.clear_hard_def ();
	  ii.merge (pp);

	  if (LABEL_P(insn))
	    {
	      /* work on all jumps referring to that label. */
	      l2j_iterator i = label2jump.find (insn->u2.insn_uid);

	      /* no jump to here -> mark all registers as hard regs.
	       * This label is maybe used in an exception handler.
	       * Marking as hard also avoids stack frame removal.
	       */
	      if (i == label2jump.end ())
		infos[pos + 1].make_hard ();
	      else
		for (l2j_iterator k = i; i != label2jump.end () && i->first == k->first; ++i)
		  {
		    i2i_iterator j = insn2info.find (i->second);
		    if (j != insn2info.end ())
		      {
			unsigned index = j->second->get_index ();
			insn_info & jj = infos[index];
			if (!jj.is_visited () || !jj.contains (ii))
			  {
			    jj.updateWith (ii);
			    todo.insert (index);
			  }
		      }
		  }

	      if (pos == start)
		pp.mark_visited ();

	      /* check previous insn for jump */
	      if (pos > 0 && infos[pos - 1].is_jump ())
		{
		  rtx_insn * prev = infos[pos - 1].get_insn ();
		  rtx set = single_set (prev);
		  /* unconditional? -> break! */
		  if (set && SET_DEST(set) == pc_rtx && GET_CODE(SET_SRC(set)) != IF_THEN_ELSE)
		    break;
		}

	      continue;
	    }

	  pp.mark_visited ();

	  rtx pattern = PATTERN (insn);
	  insn_info use (insn);
	  use.scan ();
	  if (locka4 && (use.get_myuse () & (1 << PIC_REG)))
	    use.mark_hard (PIC_REG);

	  /* do not mark a node as visited, if it's in epilogue and not yet visited. */
	  if (CALL_P(insn) || JUMP_P(insn))
	    {
	      if (pos != start && ii.in_proepi ())
		{
		  su_iterator k = scan_starts.find (pos);
		  if (k != scan_starts.end ())
		    {
		      pp.clear_visited ();
		      break;
		    }
		}
	    }
	  else if (GET_CODE (pattern) == USE || GET_CODE (pattern) == CLOBBER)
	    {
	      use.make_clobber ();
	    }
	  else if (single_set (insn) == 0)
	    use.make_hard ();

	  // TODO: use 2 bits for data regs, to indicate mode size
//	  // also check mode size if < 4, it's also a use for data registers.
//	  if (pp.get_dst_reg () && pp.get_dst_regno () < 8 && GET_MODE_SIZE(pp.get_mode()) < 4)
//	    use.mark_use (pp.get_dst_regno ());

	  /* mark not renameable in prologue/epilogue. */
	  if (pp.in_proepi () != IN_CODE)
	    use.make_hard ();

	  ii.merge (use);
	  pp.update (ii);
	  ii.updateWith (use);
	}
    }

  /* fill the mask of regs which are assigned a value. */
  insn_info zz;
  for (unsigned i = 0; i < infos.size (); ++i)
    {
      insn_info & ii = infos[i];
      if (ii.in_proepi ())
	continue;

      zz.or_def (ii);
    }

  /* always allow a0/a1, d0/d1. */
  usable_regs = zz.get_def () | 0x303;
  usable_regs &= 0x7fff;

  /* do not use global registers. */
  for (unsigned i = 0, j = 1; i < FIRST_PSEUDO_REGISTER; ++i)
    {
      if (global_regs[i])
	usable_regs &= ~j;
      j <<= 1;
    }
}

enum AbortCodes
{
  E_OK, E_NO_JUMP_LABEL, E_JUMP_TABLE_MISMATCH, E_JUMP_GOTO_LABEL, E_SP_MISMATCH
};

/*
 * Create a filtered view of insns - keep only those to work with.
 */
static unsigned
update_insns ()
{
  rtx_insn *insn, *next;
  unsigned result = 0;

  clear ();

  enum proepis inproepilogue = IN_PROLOGUE;
  /* create a vector with relevant insn. */
  for (insn = get_insns (); insn; insn = next)
    {
      next = NEXT_INSN (insn);

      if (NONJUMP_INSN_P (insn) || LABEL_P(insn) || JUMP_P(insn) || CALL_P(insn))
	{

	  infos.push_back (insn_info (insn, inproepilogue));
	  insn_info & ii = infos[infos.size () - 1];

	  if (JUMP_P(insn))
	    {
	      if (inproepilogue || ANY_RETURN_P(PATTERN (insn)))
		{
		  if (ANY_RETURN_P(PATTERN (insn)))
		    ii.set_proepi (IN_EPILOGUE);

		  scan_starts.insert (infos.size () - 1);
		  inproepilogue = IN_CODE;
		  rtx set = single_set (insn);
		  if (ANY_RETURN_P(PATTERN (insn))
		      || (set && SET_DEST(set) == pc_rtx && GET_CODE(SET_SRC(set)) != IF_THEN_ELSE))
		    continue;
		}

	      ii.mark_jump ();

	      rtx table = 0;
	      rtx_insn * label = (rtx_insn *) JUMP_LABEL(insn);
	      if (label &&  NEXT_INSN (label) && JUMP_TABLE_DATA_P (NEXT_INSN (label)))
		table = PATTERN(NEXT_INSN (label));
	      if (table)
		{
		  // -> jump_table_data
		  if (GET_CODE(table) == ADDR_DIFF_VEC || GET_CODE(table) == ADDR_VEC)
		    {
		      int k = GET_CODE(table) == ADDR_DIFF_VEC;
		      for (int j = 0; j < XVECLEN(table, k); ++j)
			{
			  rtx ref = XVECEXP(table, k, j);
			  if (!LABEL_REF_NONLOCAL_P(ref))
			    {
			      rtx label = XEXP(ref, 0);
			      label2jump.insert (std::make_pair (label->u2.insn_uid, insn));
			      ii.set_proepi (IN_EPILOGUE);
			    }
			}
		    }
		  else
		    {
		      if (be_very_verbose)
			{
			  debug_rtx (insn);
			  debug_rtx (table);
			}
		      result = E_JUMP_GOTO_LABEL;
		      continue;
		    }
		}
	      else
		{
		  rtx_insn * label = (rtx_insn *) JUMP_LABEL(insn);
		  if (!label)
		    {
		      if (be_very_verbose)
			debug_rtx (insn);
		      result = E_NO_JUMP_LABEL;
		      continue;
		    }
		  label2jump.insert (std::make_pair (label->u2.insn_uid, insn));
		}
	    }
	  else if (LABEL_P(insn))
	    {
	      ii.mark_label ();
	      ii.set_proepi (inproepilogue = IN_CODE);
	      if (infos.size () > 1)
		scan_starts.insert (infos.size () - 1);
	    }
	  else if (CALL_P(insn))
	    {
	      if (insn->jump)
		{
		  ii.set_proepi (IN_EPILOGUE);
		  ii.mark_jump ();
		  scan_starts.insert (infos.size () - 1);
		}
	      ii.mark_call ();
	      if (inproepilogue)
		{
		  scan_starts.insert (infos.size () - 1);
		  inproepilogue = IN_CODE;
		}
	    }
	  else
	    {
	      rtx set = single_set (insn);
	      if (set)
		ii.fledder (set);
	    }
	}
      else if (NOTE_P(insn))
	{
	  if (NOTE_KIND(insn) == NOTE_INSN_PROLOGUE_END)
	    inproepilogue = IN_CODE;
	  else if (NOTE_KIND(insn) == NOTE_INSN_EPILOGUE_BEG)
	    inproepilogue = IN_EPILOGUE;
	}
    }
  scan_starts.insert (infos.size () - 1);
  update_insn2index ();
  update_insn_infos ();

  return result;
}

/* convert the lowest set bit into a register number. */
static int
bit2regno (unsigned bit)
{
  if (!bit)
    return -1;

  unsigned regno = 0;
  while (!(bit & 1))
    {
      ++regno;
      bit >>= 1;
    }
  return regno;
}

/* check if that register is touched between from and to, excluding from and to .*/
static bool
is_reg_touched_between (unsigned regno, int from, int to)
{
  for (int index = from + 1; index < to; ++index)
    {
      insn_info & ii = infos[index];
      if (ii.is_myuse (regno) || ii.is_def (regno))
	return true;
    }
  return false;
}

/*
 * search backward and find the initial assignment for that regno.
 */
static unsigned
find_start (unsigned start, unsigned rename_regno)
{
  /* search the start. */
  while (start > 0)
    {
      unsigned startm1 = start - 1;

      insn_info & jj = infos[start];

      /* stop at labels. If a label is a start pos, a search is maybe started again. */
      if (jj.is_label ())
	break;

      /* do not run over RETURNS */
      insn_info & bb = infos[startm1];
      if (jj.in_proepi () == IN_CODE && bb.in_proepi () >= IN_EPILOGUE)
	break;

      /* found the definition without use. */
      if (jj.is_def (rename_regno) && !jj.is_use (rename_regno))
	break;

      start = startm1;
    }
  return start;
}

/*
 * Always prefer lower register numbers within the class.
 */
static unsigned
opt_reg_rename (void)
{
  update_label2jump ();

  if (infos.size () < 2)
    return 0;

  unsigned changes = 0;

//  dump_insns ("rename", 1);
  for (unsigned index = 0; index < infos.size (); ++index)
    {
      insn_info & ii = infos[index];

      /* do not rename if register is hard or used in same statement. */
      const unsigned rename_regbit = ii.get_regbit ();
      if (!rename_regbit)
	continue;

      const unsigned rename_regno = bit2regno (rename_regbit);

      /* part of multi registers? do not touch! */
      if (ii.get_multi_reg () & rename_regbit)
	continue;

      /* get the mask for free registers. */
      unsigned mask = ii.get_free_mask ();

      /* the mask contains the current src register. Add this register to the mask if it's dead here. */
      if (ii.get_src_reg () && is_reg_dead (ii.get_src_regno (), index))
        mask |= ii.get_use ();

      mask &= usable_regs;

      /* do not use a4 if compiling baserel */
      if (flag_pic >= 3)
	mask &= ~(1 << PIC_REG);

      if (!mask)
	continue;

      /* first = pos to start, second indicates to treat def as use. */
      std::set<unsigned> todo;
      std::set<unsigned> found;
      if (index + 1 < infos.size ())
	todo.insert (index + 1);

      found.insert (index);
      /* a register was defined, follow all branches. */
      while (mask && todo.begin () != todo.end ())
	{
	  unsigned runpos = *todo.begin ();
	  todo.erase (todo.begin ());

//	  printf ("runpos %d \n", runpos); fflush (stdout);
	  for (unsigned pos = runpos; mask && pos < infos.size (); ++pos)
	    {
	      /* already searched. */
	      if (found.find (pos) != found.end ())
		break;

	      insn_info & jj = infos[pos];
	      if (jj.is_call()) {
		  // do not rename registers used or defined in calls
		  if (jj.is_myuse(rename_regno) || jj.is_def(rename_regno)) {
		    mask = 0;
		    break;
		  }
	      }

	      rtx_insn * insn = jj.get_insn ();
	      if (LABEL_P(insn))
		{
		  found.insert (pos);

		  /* for each jump to this label:
		   * check if the reg was used at that jump.
		   * if used, find def
		   */
		  for (l2j_iterator i = label2jump.find (insn->u2.insn_uid), k = i;
		      i != label2jump.end () && i->first == k->first; ++i)
		    {
		      i2i_iterator j = insn2info.find (i->second);
		      if (j == insn2info.end ())
			{
			  mask = 0;
			  break;
			}

		      unsigned startat = j->second->get_index ();
		      if (found.find (startat) != found.end () || !infos[startat].is_use (rename_regno))
			continue;

		      unsigned start = find_start (startat, rename_regno);
//		      printf ("label %d <- jump %d : start %d\n", pos, startat, start); fflush (stdout);
		      todo.insert (start);
		    }

		  /* if this label is at a start, check if it is reachable from the previous insn,
		   * and if, check for use then search start. */
		  if (pos > 0)
		    {
		      insn_info & bb = infos[pos - 1];
		      rtx set = single_set (bb.get_insn ());
		      if (ANY_RETURN_P(bb.get_insn ())
			  || (set && SET_DEST(set) == pc_rtx && GET_CODE(SET_SRC(set)) != IF_THEN_ELSE))
			continue;

//		      printf ("label start check %d use %d\n", pos, bb.is_use (rename_regno) || bb.is_def(rename_regno)); fflush (stdout);

		      // search previous insn if it's a label or the register is used or defined.
		      if (bb.is_label() || bb.is_use (rename_regno) || bb.is_def (rename_regno))
			{
			  unsigned start = find_start (pos - 1, rename_regno);
			  todo.insert (start);
//			  printf ("label %d : start %d \n", pos, start); fflush (stdout);
			}
		    }

		  continue;
		}

	      /* marked as hard reg -> invalid rename */
	      if ((jj.get_use () & jj.get_hard () & rename_regbit)
		      /* or register is used and defined - with double register usage. */
		  || (jj.get_multi_reg () & rename_regbit))
		{
		  mask = 0;
		  break;
		}

	      /* not used. and not a def */
	      if (pos == runpos && (jj.get_def () & rename_regbit))
		{
		  /* continue since this pos was added by start search. */
		}
	      else if (!(jj.get_use () & rename_regbit))
		break;

	      /* abort if some insn using this reg uses more than 1 reg. */
	      if ((jj.get_myuse () & rename_regbit) && GET_MODE_SIZE(jj.get_mode()).to_constant() > 4)
		{
		  mask = 0;
		  break;
		}

	      /* update free regs. */
	      mask &= ~jj.get_use ();
	      mask &= ~jj.get_def ();
	      mask &= ~jj.get_multi_reg();
	      if (!mask)
		break;

	      found.insert (pos);

	      /* follow jump and/or next insn. */
	      if (JUMP_P(insn))
		{
		  for (j2l_iterator i = jump2label.find (pos), k = i; i != jump2label.end () && i->first == k->first;
		      ++i)
		    {
		      unsigned label_index = i->second;

		      /* add the label to the search list. */
		      int labi = 0;

		      // search next non-label insn
		      insn_info * bb;
		      do
		        bb = &infos[label_index + ++labi];
		      while (bb->is_label());

		      if (found.find (label_index) == found.end () && bb->is_use (rename_regno))
			{
//			  printf ("jump %d -> label %d \n", pos, label_index); fflush (stdout);
			  todo.insert (label_index);
			}
		    }
		  rtx set = single_set (insn);
		  if (!set)
		    {
		      // it's a parallel pattern - search the set pc = ...
		      rtx pat = PATTERN (insn);
		      for (int j = XVECLEN (pat, 0) - 1; j >= 0; j--)
			{
			  rtx x = XVECEXP(pat, 0, j);
			  if (XEXP(x, 0) == pc_rtx)
			    {
			      set = x;
			      break;
			    }
			}
		    }
		  rtx jmpsrc = set ? SET_SRC(set) : 0;
		  if (!jmpsrc || GET_CODE(jmpsrc) != IF_THEN_ELSE)
		    break;
		}
	    }
	}

      while (mask && found.size() > 1)
	{
	  int oldregno = bit2regno (rename_regbit);
	  int newregno = bit2regno (mask);

	  /* check the renamed insns. */
	  std::vector<unsigned> positions;
	  std::set<machine_mode> modes;
//	  bool ok = true;
	  for (std::set<unsigned>::iterator i = found.begin (); i != found.end (); ++i)
	    {
	      insn_info & rr = infos[*i];

//	      // prevent lea from or to data register.
//	      if (rr.get_src_op() == PLUS && rr.get_src_regno() != rr.get_dst_regno()) {
//		  if ((oldregno < 8 && newregno >= 8) || (oldregno >= 8 && newregno < 8)) {
//		      ok = false;
//		      break;
//		  }
//	      }

	      rtx_insn * insn = rr.get_insn ();

	      /* get rename modes. */
	      modes.clear();
	      find_reg_modes_by_no (PATTERN (insn), oldregno, modes);
	      if (modes.size() > 0)
		{
		  for (std::set<machine_mode>::iterator m = modes.begin(); m != modes.end(); ++m)
		    {
		      machine_mode mode = *m;
		      rtx to = gen_raw_REG (mode, newregno);
		      rtx from = gen_raw_REG (mode, oldregno);

		      validate_replace_rtx_group (from, to, insn);
		    }
		  positions.push_back (*i);
		}
	    }

	  if (apply_change_group ())
	    {
	      log ("(r) opt_reg_rename %s -> %s (%d locs, start at %d)\n", reg_names[oldregno], reg_names[newregno],
		   positions.size (), index);

	      if (be_verbose)
		{
		  for (std::vector<unsigned>::iterator i = positions.begin (); i != positions.end (); ++i)
		    printf ("%d ", *i);
		  printf ("\n");
		  fflush (stdout);
		}
#if 0
	      unsigned oldbit = 1 << oldregno;
	      unsigned newbit = 1 << newregno;
	      // update the insn_infos
	      for (std::vector<unsigned>::iterator i = positions.begin (); i != positions.end (); ++i)
		{
		  insn_info & pp = infos[*i];
		  if (pp.get_def() & oldbit)
		    {
		      pp.set_def((pp.get_def() & ~oldbit) | newbit);
		    }
		  if (pp.get_use() & oldbit)
		    {
		      pp.set_use((pp.get_use() & ~oldbit) | newbit);
		    }
		  if (pp.get_myuse() & oldbit)
		    {
		      pp.set_myuse((pp.get_myuse() & ~oldbit) | newbit);
		    }
		}

	      // continue
	      ++changes;
	      break;
#else
	      return 1;
#endif
	    }
//	  if (!ok)
//	    cancel_changes (0);

	  // try next register in mask - but skip those of same kind
	  if (newregno < 8)
	    mask &= 0xffff00;
	  else
	    mask &= 0xff0000;
	}
    }
  return changes;
}

/*
 *  #1 propagate a->b->a moves out of a loop.
 *
 * consider a loop:
 *
 * .L1
 *   ...
 *   move d0, a0 ; (1)
 *   ...
 *   move xy, (a0)+
 *   ...
 *   move a0, d0 ; (2)
 *   ...
 *   jxx .L1
 *
 *  Then the statements (1) and (2) can be moved out of the loop:
 *
 *   move d0, a0 ; (3)
 * .L1
 *   ...
 *   move *, (a0)+ ; a0 is modified somehow
 *   ...
 *   jxx .L1
 *   move a0, d0 ; (4)
 *
 *  if all criteria are met:
 *
 *  a) no other jump to .L1 -> (LABEL_NUSES(insn) == 1)
 *  b) no other use of d0 inside the loop
 *  c) no other use of a0 before (1)
 *  d) no other use of a1 after (2)
 *
 *  Optional:
 *  - omit (4) if d0 is dead
 *
 *  this will e.g. convert
 .L6:
 move.l d0,a1
 move.b (a1)+,d1
 move.l a1,d0
 move.b d1,(a0)+
 cmp.b #0, d1
 jne .L6
 *  to
 move.l d0,a1
 .L6:
 move.b (a1)+,d1
 move.b d1,(a0)+
 cmp.b #0, d1
 jne .L6

 *
 * Also allow exit jumps, if the modification of the reg is const
 * and insert a correction after the exit label.
 * The label must only be reachable by the exit jump.
 */
static unsigned
opt_propagate_moves ()
{
  unsigned change_count = 0;
  rtx_insn * current_label = 0;
  unsigned current_label_index = 0;
  std::vector<unsigned> reg_reg;
  std::vector<rtx_insn *> jump_out;

  /* start at 1 since there must be an insn before the label. */
  for (unsigned index = 1; index < infos.size (); ++index)
    {
      rtx_insn * insn = infos[index].get_insn ();

      if (LABEL_P(insn))
	{
	  if (LABEL_NUSES(insn) == 1)
	    {
	      current_label = insn;
	      current_label_index = index;
	      reg_reg.clear ();
	      jump_out.clear ();
	    }
	  else
	    current_label = 0;
	}

      if (current_label == 0)
	continue;

      if (NONJUMP_INSN_P(insn))
	{
	  // check for set reg, reg
	  rtx set = single_set (insn);
	  if (set)
	    {
	      rtx src = SET_SRC(set);
	      rtx dst = SET_DEST(set);
	      if (REG_P(src) && REG_P(dst))
		reg_reg.push_back (index);
	    }
	  else
	    current_label = 0;

	  continue;
	}

      if (JUMP_P(insn))
	{
	  rtx_insn * label = (rtx_insn *) JUMP_LABEL(insn);
	  if (label != current_label)
	    {
	      /* collect the labels for a later check if a fixup is possible. */
	      if (LABEL_NUSES(label) == 1 && BARRIER_P(PREV_INSN (label)))
		jump_out.push_back (label);
	      else
		current_label = 0;
	      continue;
	    }

	  if (reg_reg.size () > 1)
	    {
	      /* Search for reg/reg pairs. */
	      for (std::vector<unsigned>::iterator i = reg_reg.begin (); i != reg_reg.end () && i + 1 != reg_reg.end ();
		  )
		{
		  bool inc = true;
		  for (std::vector<unsigned>::iterator j = i + 1; j != reg_reg.end ();)
		    {
		      rtx_insn * ii = infos[*i].get_insn ();
		      rtx seti = single_set (ii);
		      rtx srci = SET_SRC(seti);
		      rtx dsti = SET_DEST(seti);
		      rtx_insn * jj = infos[*j].get_insn ();
		      rtx setj = single_set (jj);
		      rtx srcj = SET_SRC(setj);
		      rtx dstj = SET_DEST(setj);

		      if (rtx_equal_p (srci, dstj) && rtx_equal_p (srcj, dsti))
			{
			  /* Ensure correct usage. */
			  if (is_reg_touched_between (REGNO(srci), current_label_index, *i) // label ... move src,x
			  || is_reg_touched_between (REGNO(srci), *i, *j) // move src,x ... move x,src
			      || is_reg_touched_between (REGNO(srci), *j, index) // move x,src ... jcc
			      || is_reg_touched_between (REGNO(dsti), current_label_index, *i) // label ... move src,x
			      || is_reg_touched_between (REGNO(dsti), *j, index) // move x,src ... jcc
							 )
			    {
			      ++j;
			      continue;
			    }

			  std::vector<int> fixups;

			  /* if there are jumps out of the loop,
			   * check if the modification occurs before the jump,
			   * and if, that it's a plus const.
			   */
			  if (jump_out.size ())
			    {
			      std::vector<rtx_insn *>::iterator label_iter = jump_out.begin ();
			      int fixup = 0;

			      for (unsigned k = *i + 1; k != *j; ++k)
				{
				  rtx_insn * check = infos[k].get_insn ();
				  if (JUMP_P(check))
				    {
				      fixups.push_back (fixup);
				      if (++label_iter == jump_out.end ())
					break;
				      continue;
				    }

				  if (reg_overlap_mentioned_p (dsti, PATTERN (check)))
				    {
				      /* right now only support auto_incs. */
				      rtx set = single_set (check);
				      rtx src = SET_SRC(set);
				      rtx dst = SET_DEST(set);

				      if (reg_overlap_mentioned_p (dsti, dst))
					{
					  if (REG_P(dst))
					    break;
					  if (!MEM_P(dst))
					    break;

					  rtx x = XEXP(dst, 0);
					  if (GET_CODE(x) == REG)
					    fixup += 0; // direct use
					  else if (GET_CODE(x) == PRE_INC ||
					  GET_CODE(x) == POST_INC)
					    fixup -= GET_MODE_SIZE(GET_MODE(dst)).to_constant();
					  else if (GET_CODE(dst) == PRE_DEC ||
					  GET_CODE(dst) == POST_DEC)
					    fixup += GET_MODE_SIZE(GET_MODE(dst)).to_constant();
					  else
					    break;
					}

				      if (reg_overlap_mentioned_p (dsti, src))
					{
					  if (REG_P(src))
					    fixup += 0;
					  else
					    {
					      if (!MEM_P(src))
						break;

					      rtx x = XEXP(src, 0);
					      if (GET_CODE(x) == REG)
						fixup += 0; // direct use
					      else if (GET_CODE(x) == PRE_INC ||
					      GET_CODE(x) == POST_INC)
						fixup -= GET_MODE_SIZE(GET_MODE(dst)).to_constant();
					      else if (GET_CODE(dst) == PRE_DEC ||
					      GET_CODE(dst) == POST_DEC)
						fixup += GET_MODE_SIZE(GET_MODE(dst)).to_constant();
					      else
						break;
					    }
					}
				    }
				}
			    }

			  /* got a fixup for all jump_outs? */
			  if (fixups.size () == jump_out.size ())
			    {
			      rtx_insn * before = infos[current_label_index - 1].get_insn ();
			      rtx_insn * after = infos[index + 1].get_insn ();
//			      rtx bset = single_set (before);

			      log ("(p) propagate_moves condition met, moving regs %s, %s\n",
			      reg_names[REGNO(srci)],
				   reg_names[REGNO(dsti)]);

			      /* Move in front of loop and mark as dead. */
			      rtx_insn * newii = make_insn_raw (PATTERN (ii));
			      SET_INSN_DELETED(ii);
			      add_reg_note (newii, REG_DEAD, srci);

			      basic_block bb_before_loop = BLOCK_FOR_INSN(before);
			      edge fte = FALLTHRU_EDGE(bb_before_loop);
			      basic_block bb_glue = rtl_cfg_hooks.split_edge(fte);
			      before = BB_HEAD(bb_glue);
			      while (LABEL_P(before))
				before = NEXT_INSN(after);

			      add_insn_after (newii, before, 0);

			      /* Move behind loop. */
			      rtx_insn * newjj = make_insn_raw (PATTERN (jj));

			      while (LABEL_P(after))
				after = NEXT_INSN(after);

			      add_insn_after (newjj, after, 0);

			      SET_INSN_DELETED(jj);

			      reg_reg.erase (j);
			      reg_reg.erase (i);
			      j = reg_reg.end ();
			      inc = false;

			      /* add fixes if there were jumps out of the loop. */
			      if (jump_out.size ())
				{
				  log ("(p) propagate_moves fixing %d jump outs\n", jump_out.size ());

				  for (unsigned k = 0; k < jump_out.size (); ++k)
				    {
				      after = NEXT_INSN(jump_out[k]);
				      while (LABEL_P(after))
					after = NEXT_INSN(after);

				      if ((REGNO(dsti) < 8 || REGNO(dstj) < 8) && REGNO(dsti) != REGNO(dstj))
					{
					  rtx neu = gen_rtx_SET(
					      dstj, gen_rtx_PLUS (Pmode, dstj, gen_rtx_CONST_INT (Pmode, fixups[k])));
					  emit_insn_after (neu, after);
					  rtx move = gen_rtx_SET(dstj, dsti);
					  emit_insn_after(move, after);
					}
				      else
					{
					  rtx neu = gen_rtx_SET(
					      dstj, gen_rtx_PLUS (Pmode, dsti, gen_rtx_CONST_INT (Pmode, fixups[k])));
					  emit_insn_after (neu, after);
					}
				    }
				}
			      ++change_count;
			    }
			}
		      if (inc)
			++j;
		    }
		  if (inc)
		    ++i;
		}
	    }
	  current_label = 0;
	}
    }
  return change_count;
}

/**
 * Search for
 *
 *   mov x,reg
 *   mov reg,x
 *   cmp #0, reg
 *   jxx
 *
 * patterns.
 *
 * Use a simple state machine to find the patterns.
 */
static unsigned
opt_strcpy ()
{
  unsigned change_count = 0;
#if HAVE_cc0
  rtx_insn * x2reg = 0;
  rtx_insn * reg2x = 0;
  unsigned int regno = FIRST_PSEUDO_REGISTER;

  for (unsigned index = 0; index < infos.size (); ++index)
    {
      insn_info & ii = infos[index];
      rtx_insn * insn = ii.get_insn ();

      if (!NONJUMP_INSN_P(insn))
	{
	  x2reg = 0;
	  continue;
	}

      rtx set = single_set (insn);
      if (!set)
	{
	  x2reg = 0;
	  continue;
	}

      if (x2reg && reg2x)
	{
	  rtx src = SET_SRC(set);
	  if (GET_CODE(src) == COMPARE)
	    {
	      rtx dst = XEXP(src, 0);
	      src = XEXP(src, 1);

//	      if (CONST_INT_P(src) && INTVAL(src) == 0 && find_reg_note (insn, REG_DEAD, dst))
	      if (REG_P(dst) && CONST_INT_P(src) && INTVAL(src) == 0 && is_reg_dead (REGNO(dst), index))
		{
		  /* now check via NOTICE_UPDATE_CC*/
		  NOTICE_UPDATE_CC(PATTERN (reg2x), reg2x);
		  if (cc_status.flags == 0 && rtx_equal_p (dst, cc_status.value2))
		    {
		      rtx pattern = gen_rtx_SET(SET_DEST(single_set (reg2x)), SET_SRC(single_set (x2reg)));
		      rtx_insn * newinsn = make_insn_raw (pattern);

		      if (!insn_invalid_p (newinsn, 0))
			{
			  log ("(s) opt_strcpy condition met, removing compare and joining insns - omit reg %s\n",
			  reg_names[REGNO(dst)]);

			  SET_INSN_DELETED(x2reg);
			  SET_INSN_DELETED(reg2x);
			  SET_INSN_DELETED(insn);

			  insn = emit_insn_after (pattern, reg2x);
			  insn_invalid_p (insn, 0);

			  ++change_count;
			}
		    }
		}
	      x2reg = 0;
	      continue;
	    }
	  reg2x = 0;
	}

      /* check for reg2x first, maybe fallback to x2reg. */
      if (x2reg && reg2x == 0)
	{
	  if (REG_P(SET_SRC(set)) && REGNO(SET_SRC(set)) == regno)
	    {
	      reg2x = insn;
	      continue;
	    }
	  x2reg = 0;
	}

      /* check for a match for x2reg. */
      if (x2reg == 0)
	{
	  if (REG_P(SET_DEST(set)) && ii.get_src_op() != ASM_OPERANDS)
	    {
	      x2reg = insn;
	      reg2x = 0;
	      regno = REGNO(SET_DEST(set));
	    }
	}
    }
#endif
  return change_count;
}

/*
 * convert
 *
 * set reg1, plus (reg2, const)
 * set mem(reg2), y
 *
 * ->
 * set reg1, reg2
 * set mem(reg1+), y
 *
 * if size of postinc == const
 *
 (insn 33 32 35 4 (set (reg/v/f:SI 8 a0 [orig:47 s ] [47])
 (plus:SI (reg/v/f:SI 9 a1 [orig:46 s ] [46])
 (const_int 1 [0x1]))) sn.c:5 141 {*addsi3_internal}
 (nil))
 (insn 36 35 37 4 (set (mem:QI (reg/v/f:SI 9 a1 [orig:46 s ] [46]) [0 MEM[base: s_17, offset: 4294967295B]+0 S1 A8])
 (mem:QI (post_inc:SI (reg/v/f:SI 10 a2 [orig:53 s2 ] [53])) [0 MEM[base: s2_19, offset: 4294967295B]+0 S1 A8])) sn.c:5 46 {*m68k.md:1083}
 (expr_list:REG_INC (reg/v/f:SI 10 a2 [orig:53 s2 ] [53])
 (nil)))
 */
static unsigned
opt_commute_add_move (void)
{
  unsigned change_count = 0;

  for (unsigned index = 0; index + 1 < infos.size (); ++index)
    {
      insn_info & ii = infos[index];
      if (ii.get_dst_regno () < 8 || ii.get_dst_regno () > 15 || ii.get_src_op () != PLUS
	  || ii.get_src_regno () == ii.get_dst_regno () || !ii.get_src_intval ())
	continue;

      insn_info & jj = infos[index + 1];

      if (!jj.get_dst_mem_reg () || jj.get_dst_mem_regno () != ii.get_src_regno () || jj.get_dst_mem_addr() || jj.get_dst_autoinc()
	  || jj.get_src_regno () == ii.get_dst_regno () || GET_MODE_SIZE(jj.get_mode()).to_constant() != ii.get_src_intval ())
	continue;

      rtx_insn * insn = ii.get_insn ();

      rtx_insn * next = jj.get_insn ();
      rtx set2 = single_set (next);
      rtx dst = SET_DEST(set2);
      if (!MEM_P(dst))
	continue;

      rtx pinc = gen_rtx_POST_INC(GET_MODE(dst), ii.get_dst_reg ());
      rtx newmem = replace_equiv_address_nv (dst, pinc);

      rtx_insn * newinsn = make_insn_raw (gen_rtx_SET(ii.get_dst_reg (), ii.get_src_reg ()));

      if (!insn_invalid_p (newinsn, 1) && validate_change (next, &SET_DEST(set2), newmem, 1) && apply_change_group ())
	{
	  log ("(a) commute_add_move found\n");

	  SET_INSN_DELETED(insn);

	  insn = emit_insn_before (PATTERN(newinsn), next);

	  add_reg_note (next, REG_INC, ii.get_dst_reg ());

	  ++change_count;
	}
      else
	cancel_changes (0);
    }
  return change_count;
}

/*
 * Replace
 *
 * move x,dx
 * cmp  dx,dy
 *
 * if dx and dy are both dead after compare.
 *
 * with
 *
 * sub #n,dx
 *
 d0 d1 d2 a0 a1 a7       (insn 99 59 41 7 (set (reg:SI 2 d2)
 (const_int 1 [0x1])) sn.c:8 38 {*movsi_m68k}
 (nil))
 d0 d1 d2 a0 a1 a7       (insn 41 99 42 7 (set (cc0)
 (compare (reg/v:SI 1 d1 [orig:54 n ] [54])
 (reg:SI 2 d2))) sn.c:8 16 {*m68k.md:499}
 (expr_list:REG_DEAD (reg:SI 2 d2)
 (expr_list:REG_DEAD (reg/v:SI 1 d1 [orig:54 n ] [54])
 (nil))))
 *
 */
static unsigned
opt_const_cmp_to_sub (void)
{
  unsigned change_count = 0;
#if HAVE_cc0
  if (infos.size () < 2)
    return change_count;

  unsigned lastsub = 0;
  for (unsigned index = infos.size () - 2; index > 0; --index)
    {
      insn_info & i1 = infos[index];

      /* we wan't a compare or tst insn, */
      if (!i1.is_compare ())
	continue;

      if (GET_MODE_SIZE(i1.get_mode()).to_constant() > 4 || !i1.is_dst_reg () || REGNO(i1.get_dst_reg()) > 7)
	continue;

      /* src must be a reg dead register with a constant - or a #0 */
      if (!i1.get_src_reg () && (!i1.is_src_const () || i1.get_src_op () == PLUS))
	continue;

      /* allow an alive reg, if life ends at previous handled sub. */
      int lastsubval = 0;
      if (lastsub == index + 3)
	{
	  insn_info & pp = infos[lastsub];
	  if (pp.get_dst_regno () != i1.get_dst_regno ())
	    continue;
	  lastsubval = pp.get_src_intval ();

	  // but still check for usage after this jump
	  j2l_iterator l = jump2label.find (index + 2);
	  if (l == jump2label.end ())
	    continue;

	  insn_info & label = infos[l->second + 1];
	  if (label.is_use (i1.get_dst_regno ()))
	    continue;
	}
      else if (!is_reg_dead (i1.get_dst_regno (), index))
	continue;

      insn_info & i0 = infos[index - 1];
      int intval = 0;
      /* compare with register - check previous insn for load with constant. */
      if (i1.is_src_reg ())
	{
	  if (!is_reg_dead (i1.get_src_regno (), index))
	    continue;

	  if (GET_MODE_SIZE(i0.get_mode()).to_constant() > 4)
	    continue;

	  if (!i0.is_dst_reg () || !i0.is_src_const () || i0.get_src_op ())
	    continue;

	  if (i0.get_dst_regno () != i1.get_src_regno ())
	    continue;

	  intval = -i0.get_src_intval ();
	  if (intval < -8 || intval > 7)
	    continue;

	  /* is the next sub value in range? */
	  if (lastsub == index + 3 && (lastsubval - intval < -8 || lastsubval - intval > 7))
	    continue;
	}

      /* next insn must be the jump. */
      insn_info & i2 = infos[index + 1];
      if (!i2.is_jump ())
	continue;

      rtx jmppattern = single_set (i2.get_insn ());
      if (!jmppattern)
	continue;

      rtx jmpsrc = XEXP(jmppattern, 1);
      if (GET_CODE(jmpsrc) != IF_THEN_ELSE)
	continue;

      rtx condition = XEXP(jmpsrc, 0);
      RTX_CODE code = GET_CODE(condition);
      if (code != EQ && code != NE)
	continue;

      if (intval)
	{
	  rtx copyreg = copy_reg (i1.get_dst_reg (), -1);
	  /* create the sub statement. */
	  rtx sub = gen_rtx_PLUS(i1.get_mode (), copyreg, gen_rtx_CONST_INT (i1.get_mode (), intval));

	  rtx_insn * subinsn = make_insn_raw (gen_rtx_SET(copyreg, sub));

	  if (insn_invalid_p (subinsn, 0))
	    continue;

	  /* delete move #x,dy. */
	  SET_INSN_DELETED(i0.get_insn ())
	  /* delete cmp dx,dy */
	  SET_INSN_DELETED(i1.get_insn ());
	  /* add a cmp #0 - to be removed in final() */

	  /* convert cmp/tst into sub */
	  subinsn = emit_insn_before (PATTERN (subinsn), i1.get_insn ());
	  i1.set_insn (subinsn);

	  rtx neu = gen_rtx_SET(cc0_rtx,
				gen_rtx_COMPARE (i1.get_mode (), copyreg, gen_rtx_CONST_INT (i1.get_mode (), 0)));

	  emit_insn_before (neu, i2.get_insn ());

	  log ("(c) const_cmp_to_sub replaced %s == %s (%d) with sub %d,%s\n", reg_names[i1.get_dst_regno ()],
	  reg_names[i0.get_dst_regno ()],
	       -intval, -intval, reg_names[i1.get_dst_regno ()]);

	  if (index + 3 == lastsub)
	    {
	      /* patch previous sub - or even a compare. */
	      insn_info & pp = infos[lastsub];

	      int diff = lastsubval - intval;
	      rtx c = gen_rtx_CONST_INT (i1.get_mode (), diff);

	      if (pp.is_compare ())
		{
		  /* still a compare with 0 -> insert the sub. */
		  rtx copyreg = copy_reg (i1.get_dst_reg (), -1);
		  /* create the sub statement. */
		  rtx sub = gen_rtx_PLUS(i1.get_mode (), copyreg, c);
		  rtx set = gen_rtx_SET(copyreg, sub);
		  emit_insn_before (set, pp.get_insn ());
		}
	      else
		{
		  /* modify the sub. */
		  XEXP(SET_SRC(PATTERN(pp.get_insn())), 1) = c;
		}
	    }

	  lastsub = index;
	  ++change_count;
	}
    }
#endif
  return change_count;
}

/*
 * rare and only little gain - but :-)
 lea (-1,a0),a1
 add.l d1,a1
 subq.l #1,d1
 ->
 move.l a0,a1
 subq.l #1,d1
 add.l d1,a1
 */
static unsigned
opt_merge_add (void)
{
	return 0;
#if 0
  unsigned change_count = 0;
  for (unsigned index = 0; index + 2 < infos.size (); ++index)
    {
      insn_info & ii0 = infos[index];
      insn_info & ii1 = infos[index + 1];
      insn_info & ii2 = infos[index + 2];

      if (!ii2.is_dst_reg () || ii2.is_src_mem())
	{
	  index += 2;
	  continue;
	}

      if (!ii1.is_dst_reg () || ii1.is_src_mem())
	{
	  ++index;
	  continue;
	}

      if (!ii0.is_dst_reg () || ii0.is_src_mem() || ii0.get_src_op () != PLUS || ii1.get_src_op () != PLUS || ii2.get_src_op () != PLUS)
	continue;

      if (!ii0.is_src_const () || !ii2.is_src_const () || ii0.get_src_intval () != ii2.get_src_intval ())
	continue;

      if (ii0.get_dst_regno () != ii1.get_dst_regno () || ii1.get_src_regno () != ii2.get_dst_regno ())
	continue;

      rtx_insn * insn1 = ii1.get_insn ();

      CC_STATUS_INIT;
      NOTICE_UPDATE_CC(PATTERN (insn1), insn1);
      if (cc_status.value1 || cc_status.value2)
	continue;

      log ("(m) %d: merge_add applied\n", index);

      rtx_insn * insn0 = ii0.get_insn ();
      rtx set = PATTERN (insn0);

      // convert lea (-1,a0),a1 into move.l a0,a1
      rtx_insn * newins0 = make_insn_raw (gen_rtx_SET(XEXP(set, 0), XEXP(XEXP(set, 1), 0)));
      add_insn_after (newins0, insn0, 0);
      SET_INSN_DELETED(insn0);
      // update infos accordingly
      ii0.plus_to_move (newins0);

      rtx_insn * insn2 = ii2.get_insn ();
      rtx_insn * newins1 = make_insn_raw (PATTERN (insn1));
      add_insn_after (newins1, insn2, 0);
      SET_INSN_DELETED(insn1);
      ii1.swap_adds (newins1, ii2);

      ++change_count;
    }
  return change_count;
#endif
}

/* Update the insn_infos to 'know' the sp offset. */
static unsigned
track_sp (int & a5_touched)
{
// reset visited flags - also check if sp is used as REG src.
  for (unsigned index = 0; index < infos.size (); ++index)
    {
      insn_info & ii = infos[index];
      ii.clear_visited ();
      ii.set_sp_offset (0);

      if (ii.in_proepi() == IN_CODE)
	a5_touched |= ii.get_myuse() & 0x2000;

      // if sp is used as source, we cannot shrink the stack yet
      // too complicated - well, could be done^^
      if (ii.get_src_regno () == STACK_POINTER_REGNUM)
	return -1;
    }

// add entry point
  std::set<unsigned> todo;
  todo.insert (0);

  while (todo.begin () != todo.end ())
    {
      unsigned startpos = *todo.begin ();
      todo.erase (todo.begin ());

      int sp_offset = infos[startpos].get_sp_offset ();

      for (unsigned index = startpos; index < infos.size (); ++index)
	{
	  insn_info & ii = infos[index];
	  if (ii.in_proepi () != IN_CODE)
	    {
	      ii.set_sp_offset (sp_offset);
	      continue;
	    }

	  // already visited? sp_offset must match
	  if (ii.is_visited ())
	    {
	      if (ii.get_sp_offset () != sp_offset)
		return E_SP_MISMATCH;

	      // check all jumps to this label
	      if (ii.is_label())
		{
		  for (l2j_iterator j = label2jump.find (ii.get_insn ()->u2.insn_uid), k = j;
		      j != label2jump.end () && j->first == k->first; ++j)
		    {
		      insn_info & ll = *insn2info.find(j->second)->second;
		      if (ll.is_visited () && ll.get_sp_offset () != sp_offset)
			return E_SP_MISMATCH;
		    }
		}

		// check the label(s) for this jump
		if (ii.is_jump ())
		  {
		    for (j2l_iterator i = jump2label.find (index), k = i; i != jump2label.end () && i->first == k->first; ++i)
		      {
			insn_info & ll = infos[i->second];
			if (ll.is_visited () && ll.get_sp_offset () != sp_offset)
			  return E_SP_MISMATCH;
		      }
		  }

	      break;
	    }

	  // mark current insn_info and set sp_offset
	  ii.mark_visited ();
	  ii.set_sp_offset (sp_offset);

	  // add all referencing jumps
	  if (ii.is_label())
	    {
		  for (l2j_iterator j = label2jump.find (ii.get_insn ()->u2.insn_uid), k = j;
		      j != label2jump.end () && j->first == k->first; ++j)
		{
		  insn_info & ll = *insn2info.find(j->second)->second;
		  if (!ll.is_visited())
		    {
		      ll.set_sp_offset(sp_offset);
		      todo.insert (ll.get_index());
		    }
		  else if (ll.get_sp_offset() != sp_offset)
		    return E_SP_MISMATCH;
		}
	      continue;
	    }


	  // add all referred labels
	  if (ii.is_jump ())
	    {
	      for (j2l_iterator i = jump2label.find (index), k = i; i != jump2label.end () && i->first == k->first; ++i)
		{
		  insn_info & ll = infos[i->second];
		  if (!ll.is_visited())
		    {
		      ll.set_sp_offset(sp_offset);
		      todo.insert (i->second);
		    }
		  else if (ll.get_sp_offset() != sp_offset)
		    return E_SP_MISMATCH;
		}
	      continue;
	    }

	  // is sp modified directly
	  if (ii.is_dst_reg () && ii.get_dst_regno () == STACK_POINTER_REGNUM)
	    {
	      // handle sp = sp + const_int
	      if (!ii.get_src_reg () || ii.get_src_regno () != STACK_POINTER_REGNUM || ii.get_src_op () != PLUS)
		return E_SP_MISMATCH;

	      sp_offset = sp_offset + ii.get_src_intval ();
	      continue;
	    }

	  // handle dst mem autoinc
	  if (ii.is_dst_mem () && ii.get_dst_mem_regno () == STACK_POINTER_REGNUM && ii.get_dst_autoinc ())
	    sp_offset += GET_MODE_SIZE(ii.get_mode()).to_constant() * ii.get_dst_autoinc ();

	  // handle src mem autoinc
	  if (ii.is_src_mem () && ii.get_src_mem_regno () == STACK_POINTER_REGNUM && ii.get_src_autoinc ())
	    sp_offset += GET_MODE_SIZE(ii.get_mode()).to_constant() * ii.get_src_autoinc ();
	}
    }

  return 0;
}

/* recursive function to patch stack pointer offsets. */
void
patch_sp (rtx x, int adjust, int spoffset)
{
  int code = GET_CODE(x);
  if (code == PLUS)
    {
      rtx a = XEXP(x, 0);
      rtx b = XEXP(x, 1);
      if (REG_P(a) && REGNO(a) == STACK_POINTER_REGNUM && GET_CODE(b) == CONST_INT)
	{
	  if (INTVAL(b) > -spoffset)
	    XEXP(x, 1) = gen_rtx_CONST_INT (GET_MODE(b), INTVAL(b) - adjust);
	  return;
	}
    }
  const char *fmt = GET_RTX_FORMAT(code);
  for (int i = GET_RTX_LENGTH (code) - 1; i >= 0; i--)
    {
      if (fmt[i] == 'e')
	patch_sp (XEXP(x, i), adjust, spoffset);
      else if (fmt[i] == 'E')
	for (int j = XVECLEN (x, i) - 1; j >= 0; j--)
	  patch_sp (XVECEXP(x, i, j), adjust, spoffset);
    }
}

/**
 * 1. scan for all used registers.
 * 2. scan the stack from for omittable push/pop
 * 3. adjust stack frame + insns referring to stack pointer
 * typical code:
 subq.l #4,sp
 movem.l #16190,-(sp)
 move.l 52(sp),d2
 move.l 56(sp),d3

 * or
 link a5,#4
 movem.l #16190,-(sp)
 move.l 8(a5),d2
 move.l 12(a5),d3
 *
 * => with a5 check only prolog/epilog
 * => without a5 adjust insns referring sp if offset > startoffset + current sp diff
 *
 * startvalue count(pushes)*4
 * newstartvalue = startvalue - omitted pushes
 */
static unsigned
opt_shrink_stack_frame (void)
{
  /* nothing to do. */
  if (!infos.size ())
    return 0;

  /* needed to track sp correctly. */
  update_label2jump ();
  int a5_touched = 0;
  if (track_sp (a5_touched))
    return 0; // do nothing on stack errors

  std::vector<int> a5pos;

  unsigned pos = 0;
  rtx_insn * insn = infos[pos].get_insn ();
  if (JUMP_P(insn)) /* return -> empty function*/
    return 0;

  bool usea5 = false;
  int paramstart = 4;
  int a5offset = 0;

  /*
   * Move prologue to temp.
   * Only register push and parallel insn unless its a link a5 are moved.
   */
  for (; pos < infos.size ();)
    {
      insn_info & ii = infos[pos];
      insn = ii.get_insn ();

      if (ii.in_proepi () != IN_PROLOGUE)
	break;

      rtx pattern = PATTERN (insn);
      if (GET_CODE(pattern) == PARALLEL)
	{
	  rtx set = XVECEXP(pattern, 0, 0);
	  rtx dst = SET_DEST(set);
	  ii.mark_stack ();
	  /* ignore link a5 */
	  if (REG_P(dst) && REGNO(dst) == FRAME_POINTER_REGNUM)
	    {
	      a5pos.push_back (pos);
	      usea5 = true;
	      set = XVECEXP(pattern, 0, 2);
	      a5offset = INTVAL(XEXP(SET_SRC(set), 1));
	    }
	  ++pos;
	  continue;
	}
      if (GET_CODE(pattern) != SET)
	{
	  /* (set (mem:BLK (scratch) [0  A8]) (unspec:BLK [ ...)) */
	  if (MEM_P(SET_DEST(pattern)) && GET_CODE(SET_SRC(pattern)) == UNSPEC)
	    a5pos.push_back (pos);
	  ++pos;
	  continue;
	}

      /* move only the push statements. */
      rtx src = SET_SRC(pattern);
      rtx dest = SET_DEST(pattern);
      if (REG_P(src))
	{
	  if (MEM_P(dest))
	    {
	      rtx predec = XEXP(dest, 0);
	      if (GET_CODE(predec) == PRE_DEC)
		{
		  rtx reg = XEXP(predec, 0);
		  if (REG_P(reg) && REGNO(reg) == STACK_POINTER_REGNUM)
		    {
		      ii.mark_stack ();
		    }
		}
	    }
	}
      else if (GET_CODE(src) == PLUS && REG_P(dest) && REGNO(dest) == STACK_POINTER_REGNUM)
	{
	  /* check for stack variables. */
	  rtx reg = XEXP(src, 0);
	  rtx cx = XEXP(src, 1);
	  if (REG_P(reg) && REGNO(reg) == STACK_POINTER_REGNUM && CONST_INT_P(cx))
	    paramstart -= INTVAL(cx);
	}

      if (++pos >= infos.size ())
	{
	  return 0;
	}
    }

  if (pos == 0)
    return 0;

  unsigned prologueend = pos;

  /* search epilogues - there can be multiple epilogues. */
  while (pos < infos.size ())
    {
      while (pos < infos.size ())
	{
	  if (infos[pos].in_proepi () != IN_CODE)
	    break;
	  ++pos;
	}

      /* move epilogues away. */
      for (; pos < infos.size (); ++pos)
	{
	  insn_info & ii = infos[pos];
	  insn = ii.get_insn ();
	  if (JUMP_P(insn) || LABEL_P(insn) || ii.in_proepi () == IN_CODE)
	    break;

	  /* omit the frame pointer a5. */
	  rtx pattern = PATTERN (insn);
	  if (GET_CODE(pattern) == PARALLEL)
	    {
	      rtx set = XVECEXP(pattern, 0, 0);
	      rtx dst = SET_DEST(set);
	      ii.mark_stack ();
	      /* unlink is last. */
	      if (REG_P(dst) && REGNO(dst) == FRAME_POINTER_REGNUM)
		{
		  a5pos.push_back (pos);
		  break;
		}

	    }
	  else if (GET_CODE(pattern) == SET)
	    {
	      /* check for move (a7+), x */
	      rtx src = SET_SRC(pattern);
	      rtx dst = SET_DEST(pattern);
	      if (REG_P(dst))
		{
		  if (MEM_P(src))
		    {
		      rtx postinc = XEXP(src, 0);
		      if (GET_CODE(postinc) == POST_INC)
			{
			  rtx reg = XEXP(postinc, 0);
			  if (REG_P(reg) && REGNO(reg) == STACK_POINTER_REGNUM)
			    ii.mark_stack ();
			}
		      else if (GET_CODE(postinc) == PLUS)
			{
			  rtx a5 = XEXP(postinc, 0);
			  if (REG_P(a5) && REGNO(a5) == FRAME_POINTER_REGNUM)
			    ii.mark_stack ();
			}
		    }
		}
	    }
	}
      ++pos;
    }

  unsigned freemask = 0x7fff & ~usable_regs;

  /* do not remove a4 push/pop in baserel modes, if __saveds or commandline demands it. */
  if (flag_pic > 2)
    {
      tree attrs = TYPE_ATTRIBUTES (TREE_TYPE (current_function_decl));
      tree attr = lookup_attribute ("saveds", attrs);
      if (attr || TARGET_RESTORE_A4 || TARGET_ALWAYS_RESTORE_A4)
	freemask &= ~(1 << PIC_REG);
    }

  rtx a7 = gen_raw_REG (E_SImode, STACK_POINTER_REGNUM);
  rtx a5 = gen_raw_REG (E_SImode, FRAME_POINTER_REGNUM);

  unsigned changed = 0;
  unsigned adjust = 0;
  unsigned regs_seen = 0;
  unsigned regs_total_size = 0;
  /* now all push/pop insns are in temp. */
  for (unsigned i = 0; i < infos.size (); ++i)
    {
      insn_info & ii = infos[i];
      if (!ii.is_stack ())
	continue;

      insn = ii.get_insn ();
      rtx pattern = PATTERN (insn);
      /* check the pushed regs, either a vector or single statements */
      if (GET_CODE(pattern) == PARALLEL)
	{
	  // do not touch the frame pointer parallel insn.
	  rtx set = XVECEXP(pattern, 0, 0);
	  rtx dst = SET_DEST(set);
	  if (REG_P(dst) && REGNO(dst) == FRAME_POINTER_REGNUM)
	    continue;

	  if (ii.in_proepi () == IN_EPILOGUE)
	    ii.set_proepi (IN_EPILOGUE_PARALLEL_POP);

	  regs_seen = 0;
	  regs_total_size = 0;
	  std::vector<rtx> regs;
	  std::vector<rtx> clobbers;
	  for (int j = 0; j < XVECLEN(pattern, 0); ++j)
	    {
	      rtx set = XVECEXP(pattern, 0, j);
	      if (GET_CODE(set) == CLOBBER)
		{
		  clobbers.push_back (set);
		  continue;
		}
	      rtx dst = SET_DEST(set);
	      rtx src = SET_SRC(set);
	      rtx reg;
	      if (MEM_P(src))
		reg = dst;
	      else if (MEM_P(dst))
		reg = src;
	      else
		continue;

	      if (i < prologueend)
		paramstart += 4;
	      unsigned regbit = 1 << REGNO(reg);

	      ++regs_seen;
	      if (freemask & regbit)
		{
		  log (i < prologueend ? "(f) remove push for %s\n" : "(f) remove pop for %s\n",
		  reg_names[REGNO(reg)]);
		  if (i < prologueend)
		    adjust += GET_MODE_SIZE(GET_MODE(reg)).to_constant();
		}
	      else
		{
		  regs_total_size += GET_MODE_SIZE(GET_MODE(reg)).to_constant();
		  regs.push_back (copy_reg (reg, -1));
		}
	    }

	  /* add room for add.
	   * push is always using -(a7) addressing.
	   * If a5 is used a movem offset(a5) is generated to pop saved registers..
	   * Otherwise a7 is used and with (a7)+ addressing.
	   */
	  int add1 = i < prologueend || !(ii.get_myuse () & (1 << FRAME_POINTER_REGNUM)) ? 1 : 0;
	  if (regs.size () < regs_seen)
	    {
	      log ("(f) shrinking stack frame from %d to %d\n", regs_seen, regs.size ());
	      if (regs.size () <= 2)
		{
		  int x = 0;
		  for (unsigned k = 0; k < regs.size (); ++k)
		    x -= REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
		  changed = 1;
		  for (unsigned k = 0; k < regs.size (); ++k)
		    {
		      rtx reg = regs[k];
		      if (i < prologueend)
			{
			  /* push */
			  rtx dec = gen_rtx_PRE_DEC(REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, a7);
			  rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, dec);
			  rtx set = gen_rtx_SET(mem, reg);
			  emit_insn_after (set, insn);
			}
		      else
			{
			  if ((ii.get_myuse () & (1 << FRAME_POINTER_REGNUM))
			      && (a5offset != -4 || a5_touched)) // no conversion to sp)
			    {
			      /* pop via a5 + offset*/
			      x += REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			      rtx plus = gen_rtx_PLUS(E_SImode, a5, gen_rtx_CONST_INT (E_SImode, a5offset + x));
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, plus);
			      rtx set = gen_rtx_SET(reg, mem);
			      emit_insn_before (set, insn);
			    }
			  else
			    {
			      /* pop */
			      rtx dec = gen_rtx_POST_INC(REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, a7);
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, dec);
			      rtx set = gen_rtx_SET(reg, mem);
			      emit_insn_before (set, insn);
			    }
			}
		    }
		}
	      else
		{
		  rtx parallel = gen_rtx_PARALLEL(VOIDmode, rtvec_alloc (regs.size () + add1 + clobbers.size ()));
		  rtx plus;

		  int x = 0;
		  for (unsigned k = 0; k < regs.size (); ++k)
		    x += REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;

		  unsigned l = 0;
		  /* no add if a5 is used with pop */
		  if (add1)
		    {
		      plus = gen_rtx_PLUS(E_SImode, a7, gen_rtx_CONST_INT (E_SImode, i < prologueend ? -x : x));
		      XVECEXP(parallel, 0, l) = gen_rtx_SET(a7, plus);
		      ++l;
		    }

		  if (i >= prologueend)
		    x = (ii.get_myuse () & (1 << FRAME_POINTER_REGNUM)) ? -x : 0;


		  for (unsigned k = 0; k < regs.size (); ++k, ++l)
		    {
		      if (i < prologueend)
			{
			  /* push */
			  plus = gen_rtx_PLUS(E_SImode, a7, gen_rtx_CONST_INT (E_SImode, -x));
			  x -= REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			  rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, plus);
			  rtx set = gen_rtx_SET(mem, regs[k]);
			  XVECEXP(parallel, 0, l) = set;
			}
		      else
			{
			  /* pop - use the same register as in the existing insn*/
			  if (ii.get_myuse () & (1 << FRAME_POINTER_REGNUM))
			    {
			      x += REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			      plus = gen_rtx_PLUS(E_SImode, a5, gen_rtx_CONST_INT (E_SImode, a5offset + x));
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, plus);
			      rtx set = gen_rtx_SET(regs[k], mem);
			      XVECEXP(parallel, 0, l) = set;
			    }
			  else
			    {
			      plus = x ? gen_rtx_PLUS(E_SImode, a7, gen_rtx_CONST_INT (E_SImode, x)) : a7;
			      x += REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? E_XFmode : E_SImode, plus);
			      rtx set = gen_rtx_SET(regs[k], mem);
			      XVECEXP(parallel, 0, l) = set;
			    }
			}
		    }

		  for (unsigned k = 0; k < clobbers.size (); ++k, ++l)
		    {
		      rtx clobber = clobbers[k];
		      XVECEXP(parallel, 0, l) = clobber;
		    }

		  rtx_insn * neu;
		  if (i < prologueend)
		    neu = emit_insn_after (parallel, insn);
		  else
		    neu = emit_insn_before (parallel, insn);
		  ii.set_insn (neu);
		}
	      SET_INSN_DELETED(insn);
	      changed = 1;
	    }
	}
      else
	{
	  // shrink from 2/1 to 1/0

	  rtx set = PATTERN (insn);

	  if (i < prologueend)
	    {
	      /* move x,-(a7). */
	      rtx src = SET_SRC(set);
	      paramstart += REGNO(src) > STACK_POINTER_REGNUM ? 12 : 4;
	      unsigned regbit = 1 << REGNO(src);
	      if (freemask & regbit)
		{
		  adjust += REGNO(src) > STACK_POINTER_REGNUM ? 12 : 4;
		  log ("(f) remove push for %s\n", reg_names[REGNO(src)]);
		  SET_INSN_DELETED(insn);
		  ++changed;
		}
	      else
		{
		  regs_total_size += GET_MODE_SIZE(GET_MODE(src)).to_constant();
		}
	    }
	  else
	    {
	      /* move (a7)+,x */
	      rtx dst = SET_DEST(set);
	      unsigned regbit = 1 << REGNO(dst);
	      if (freemask & regbit)
		{
		  log ("(f) remove pop for %s\n", reg_names[REGNO(dst)]);
		  SET_INSN_DELETED(insn);
		  ++changed;

		  if ((ii.get_myuse () & (1 << FRAME_POINTER_REGNUM)))
		    {
		      rtx x;
		      // the previous offset needs a fix if it's also a a5 pop
		      insn_info & pp = infos[i - 1];
		      if (pp.is_stack() && (set = single_set(pp.get_insn())) && MEM_P(x = SET_SRC(set))
			  && GET_CODE(x = XEXP(x, 0)) == PLUS && REG_P(XEXP(x, 0)) && REGNO(XEXP(x, 0)) == FRAME_POINTER_REGNUM)
			{
			  XEXP(x, 1) = GEN_INT(INTVAL(XEXP(x, 1)) + GET_MODE_SIZE(GET_MODE(SET_SRC(set))).to_constant());
			}
		    }

		}
	    }
	}
    }

  /* fix sp offsets. */
  if (!usea5 && adjust)
    {
      for (unsigned index = 0; index < infos.size (); ++index)
	{
	  insn_info & ii = infos[index];
	  if (ii.in_proepi () != IN_CODE)
	    continue;

	  rtx pattern = single_set (ii.get_insn ());
	  if (pattern)
	    patch_sp (pattern, adjust, ii.get_sp_offset ());
	}
    }

  if (usea5 && a5offset == -4)
    {
      /* for now only drop the frame pointer if it's not used.
       * Needs tracking of the sp to adjust the offsets.
       */
      if (!a5_touched)
	{
	  log ("(f) dropping unused frame pointer\n");
	  for (std::vector<int>::reverse_iterator i = a5pos.rbegin (); i != a5pos.rend (); ++i)
	    {
	      int index = *i;
	      SET_INSN_DELETED(infos[index].get_insn ());

	      // move to last insn in epilogue
	      while (index - 1 > 0 && infos[index - 1].in_proepi () >= IN_EPILOGUE)
		--index;

	      insn_info & ii = infos[index];
	      if (ii.in_proepi () >= IN_EPILOGUE && ii.get_sp_offset () != 0)
		{
		  log ("(f) adjusting exit sp\n");
		  rtx pattern = gen_rtx_SET(
		      a7, gen_rtx_PLUS (E_SImode, a7, gen_rtx_CONST_INT (E_SImode, -ii.get_sp_offset ())));
		  emit_insn_before (pattern, ii.get_insn ());
		}
	    }

	  /* convert all parameter accesses via a5 into a7. */
	  for (unsigned i = 0; i < infos.size (); ++i)
	    {
	      insn_info & ii = infos[i];

	      //skip already deleted insns.
	      if (GET_CODE(ii.get_insn()) == NOTE)
		continue;
	      if (ii.get_myuse () & (1 << FRAME_POINTER_REGNUM))
		{
		  ii.a5_to_a7 (a7, regs_total_size - ii.get_sp_offset());
		  if (regs_total_size && regs_seen && ii.in_proepi () == IN_EPILOGUE_PARALLEL_POP)
		    {
		      // exit sp insn needs an +
		      rtx pattern = PATTERN (ii.get_insn ());
		      unsigned sz = XVECLEN(pattern, 0);

		      rtx parallel = gen_rtx_PARALLEL(VOIDmode, rtvec_alloc (sz + 1));
		      unsigned n = 0;
		      for (unsigned j = 0; j < sz; ++j)
			{
			  rtx set = XVECEXP(pattern, 0, j);
			  rtx reg = SET_DEST(set);
			  rtx mem = SET_SRC(set);
			  rtx plus = XEXP(mem, 0);
			  if (n)
			    {
			      XEXP(plus, 1) = gen_rtx_CONST_INT (E_SImode, n);
			    }
			  else
			    {
			      XEXP(mem, 0) = XEXP(plus, 0);
			    }
			  n += GET_MODE_SIZE(GET_MODE(reg)).to_constant();
			  XVECEXP(parallel, 0, j + 1) = set;
			}

		      rtx a = copy_reg (a7, -1);
		      a->frame_related = 1;
		      rtx plus = gen_rtx_PLUS(E_SImode, a, gen_rtx_CONST_INT (E_SImode, regs_total_size));
		      rtx set = gen_rtx_SET(a, plus);
		      XVECEXP(parallel, 0, 0) = set;
		      SET_INSN_DELETED(ii.get_insn ());
		      ii.set_insn (emit_insn_after (parallel, ii.get_insn ()));
		    }
		}

	      ii.unset (FRAME_POINTER_REGNUM);
	    }

	  update_insn2index ();
	  ++changed;
	}
    }

  return changed;
}

/* Update the insn_infos to 'know' the value for each register.
 *
 * assignments to registers are optimized by knowing the value. If the same value is assigned, omit that insn.
 *
 * I'm tracking
 *
 *  rtx - the value
 *
 *  mask - the referenced registers in the value, 0 means that rtx is const, with baserel a4 is not tracked
 *
 *  if there is a value for the referenced register(s), the value is extended
 *
 * e.g.
 *
 * ; line 2
 *    move.l 12(a7),a0
 *
 * -> rtx = mem(plus(a7, 12));   0x8000
 *
 * ; line 10
 *    move.l 4(a0),d0
 *
 * -> rtx = mem(plus(mem(plus(a7, 12)), 4));   0x8000; extended with value from a0, thus a7 is used only
 *
 * ;15
 *    lea _label,a1
 *
 * -> rtx = symbol_ref(_label) ; 0x0000 == const
 *
 * on jumps the current state is duplicated and merged at the given label
 *
 * on merge only identical info is kept, rest is discarded
 *
 * for each insn for all defined regs the value and mask  is discarded before a new value is set.
 *
 * for each insn which is writing to memory, all non const values are discarded.
 *
 *
 * after the track info is complete, each insn setting a register is evaluated against the track info.
 *
 * now redundant loads are found and eliminated
 *
 */

static unsigned
track_regs ()
{
// reset visited flags
  for (unsigned index = 0; index < infos.size (); ++index)
    {
      insn_info & ii = infos[index];
      ii.clear_visited ();
      ii.set_sp_offset (0);
    }

  update_label2jump ();

// add entry point
  std::multimap<unsigned, track_var *> todo;
  todo.insert (std::make_pair (0, new track_var ()));

  while (todo.begin () != todo.end ())
    {
      unsigned startpos = todo.begin ()->first;
      track_var * const track = todo.begin ()->second;
      todo.erase (todo.begin ());

      for (unsigned index = startpos; index < infos.size (); ++index)
	{
	  insn_info & ii = infos[index];

	  // already visited?
	  if (index != startpos && ii.is_visited () && ii.get_track_var ()->no_merge_needed (track))
	    break;

	  // only keep common values at labels
	  if (ii.is_label ())
	    {
	      if (ii.is_visited ())
		{
		  ii.get_track_var ()->merge (track, index);
		}
	      else
		{
		  ii.get_track_var ()->assign (track);
		  ii.mark_visited ();
		}
	      continue;
	    }

	  // mark current insn_info and set sp_offset
	  ii.mark_visited ();
	  ii.get_track_var ()->assign (track);

	  unsigned def = ii.get_def () & 0xffffff;
	  if (def)
	    {
	      // more than one register set? or mask from clobber?
	      if (((def - 1) & def) || !ii.get_dst_reg ())
		track->clear_for_mask (def, index);
	    }

	  // compare must not clear
	  if (ii.is_compare ())
	    continue;

	  // do not clear if self assigned unless there is an operator
	  int dregno = ii.get_dst_regno ();
	  unsigned dmask = track->getMask(dregno);
	  if (dregno != ii.get_src_regno () || ii.get_src_op ())
	    track->clear (ii.get_mode (), dregno, index);


	  if (ii.is_call ())
	    {
	      track->clear_aftercall (index);
	      continue;
	    }

	  rtx set = single_set (ii.get_insn ());

	  // add all referred labels
	  if (ii.is_jump ())
	    {
	      if (ANY_RETURN_P(ii.get_insn ()))
		break;

	      for (j2l_iterator i = jump2label.find (index), k = i; i != jump2label.end () && i->first == k->first; ++i)
		todo.insert (std::make_pair (i->second, new track_var (track)));

	      if (set && GET_CODE(SET_SRC(set)) == IF_THEN_ELSE)
		continue;

	      // unconditional jump
	      break;
	    }

	  if (!set || !ii.get_def ())
	    continue;

	  if (dregno < 0)
	    {
	      track->invalidate_mem (SET_DEST(set));
	      continue;
	    }

	  if (ii.get_src_op ())
	    {
	      if (ii.get_src_op() == AND || ii.get_src_op() == IOR || ii.get_src_op() == XOR || ii.get_src_op() == PLUS)
		{
		  rtx op = XEXP(SET_SRC(set), 1);
		  unsigned mask;
		  if (GET_CODE(op) == CONST_INT)
		    mask = INTVAL(op);
		  else if (REG_P(op))
		    mask = track->getMask(REGNO(op));
		  else
		    op = 0;

		  if (op)
		    {
		      if (ii.get_src_op() == AND) {
			track->setMask(dregno, mask & dmask, ii.get_mode());
		      }
		      else if (ii.get_src_op() == IOR) {
			track->setMask(dregno, mask | dmask, ii.get_mode());
		      }
		      else if (ii.get_src_op() == XOR) {
			track->setMask(dregno, mask | dmask, ii.get_mode());
		      }
		      else if (ii.get_src_op() == PLUS) {
			track->setMask(dregno, ((mask | dmask) << 1) | 1, ii.get_mode());
		      }
		    }
		}
	      else if (ii.get_src_op() == ZERO_EXTRACT) {
		  unsigned mask = (1 << INTVAL(XEXP(SET_SRC(set), 1))) - 1;
		  track->setMask(dregno, mask, ii.get_mode());
	      }
	      else if (ii.get_src_op() == LSHIFTRT || ii.get_src_op() == ASHIFT)
		{
		  rtx op = XEXP(SET_SRC(set), 1);
		  if (GET_CODE(op) != CONST_INT)
		    {
		      if (REG_P(op))
			{
			  rtx val = track->get(REGNO(op));
			    if (val && GET_CODE(val) == CONST_INT && INTVAL(val) == (0xffff & INTVAL(val)))
			      op = val;
			    else
			      op = 0;
			}
		      else
			op = 0;
		    }
		  if (op)
		    {
		      if (GET_MODE_SIZE(ii.get_mode()).to_constant() == 2)
			dmask &= 0xffff;
		      else
		      if (GET_MODE_SIZE(ii.get_mode()).to_constant() == 1)
			dmask &= 0xff;
		      if (ii.get_src_op() == LSHIFTRT)
			track->setMask(dregno, dmask >> INTVAL(op), ii.get_mode());
		      else if (ii.get_src_op() == ASHIFT)
			track->setMask(dregno, dmask << INTVAL(op), ii.get_mode());
		    }
		}
	      continue;
	    }

	  // operation, autoinf or more than one register used: can't cache
	  if (ii.get_src_autoinc () || ((ii.get_myuse () - 1) & ii.get_myuse ()))
	    continue;

	  rtx src = SET_SRC(set);
	  if (ii.is_src_mem () && src->volatil)
	    continue;

	  track->set (ii.get_mode (), dregno, src, ii.get_myuse(), index);
	}
      delete track;
    }
  return 0;
}

/*
 * Some optimizations (e.g. propagate_moves) might result into an unused assignment behind the loop.
 * delete those insns.
 */
static unsigned
opt_elim_dead_assign (int blocked_regno)
{
  track_regs ();

  unsigned mask = 0;

  unsigned change_count = 0;
  for (int index = infos.size () - 1; index >= 0; --index)
    {
      insn_info & ii = infos[index];

      if (ii.is_compare ())
	{
	  if (blocked_regno == FIRST_PSEUDO_REGISTER && ii.get_dst_reg())
	    {
	      unsigned mask = ii.get_track_var()->getMask(ii.get_dst_regno());
	      if (mask != 0xffffffff)
		add_reg_note(ii.get_insn(), REG_BIT_MASK, gen_rtx_CONST_INT (E_SImode, mask));
	    }
	  continue;
	}

      if (ii.in_proepi () || !ii.get_dst_reg ())
	continue;

      rtx_insn * insn = ii.get_insn ();
      rtx set = single_set (insn);
      if (!set)
	continue;

      if (!ii.is_dst_reg() || ii.get_dst_regno () == blocked_regno)
	continue;

      // more than one register set? e.g. side effect move.l (a0)+,d0
      unsigned def = ii.get_def () & 0xffffff;
      if ((def - 1) & def)
	continue;

      if (GET_CODE(SET_SRC(set)) == AND)
	{
	  track_var * tv = ii.get_track_var();
	  unsigned lmask = tv->getMask(ii.get_dst_regno());
	  unsigned nmask = 0;
	  rtx andval = XEXP(SET_SRC(set), 1);

	  if (REG_P(andval))
	    {
	      rtx val = tv->get(REGNO(andval));
	      if (val && GET_CODE(val) == CONST_INT)
		{
		  long long int lli = INTVAL(val);
		  if (lli < 0x100000000LL)
		    {
		      andval = val;
		    }
		  else if (lli & 0x100000000000000LL)
		    {
		      unsigned refreg = (lli >> 32) & 0xff;
		      andval = tv->get(refreg);
		    }
		}
	    }
	  if (andval && GET_CODE(andval) == CONST_INT)
	    {
	      long long int lli = UINTVAL(andval);
	      if (lli < 0x100000000LL)
		{
		  unsigned val = lli;
		  if (GET_MODE_SIZE(ii.get_mode()).to_constant() == 1)
		    val |= 0xffffff00;
		  else if (GET_MODE_SIZE(ii.get_mode()).to_constant() < 4)
		    val |= 0xffff0000;

		  nmask = lmask & val;
		}
	    }

	  if (lmask == nmask)
	    {
	      log ("(e) %d: eliminate superfluous 'and' to %s  %08x->%08x\n",
		   index, reg_names[ii.get_dst_regno ()], lmask, nmask);
	      SET_INSN_DELETED(insn);
	      ++change_count;
	    }
	  continue;
	}

      if (mask & (1<<ii.get_dst_regno ()))
	continue;

      if (REG_NREGS(ii.get_dst_reg ()) == 1
	  && is_reg_dead (ii.get_dst_regno (), index))
	{
	  mask |= (1<<ii.get_dst_regno ());

	  log ("(e) %d: eliminate dead assign to %s\n", index, reg_names[ii.get_dst_regno ()]);
	  SET_INSN_DELETED(insn);
	  ++change_count;
	  continue;
	}

      // check for redundant load
      if (ii.get_src_op () == 0 && ii.get_dst_reg ()
	  && (!ii.is_myuse (ii.get_dst_regno ()) || ii.get_dst_regno () == ii.get_src_regno ()))
	{
	  track_var * track = ii.get_track_var ();

	  rtx src = SET_SRC(set);
	  if (track->equals (ii.get_mode(), ii.get_dst_regno (), src))
	    {
	      mask |= (1<<ii.get_dst_regno ());

	      log ("(e) %d: eliminate redundant load to %s\n", index, reg_names[ii.get_dst_regno ()]);
	      SET_INSN_DELETED(insn);
	      ++change_count;
	      continue;
	    }

	  if (ii.get_dst_regno () == ii.get_src_regno () && GET_MODE(ii.get_src_reg()) == GET_MODE(ii.get_dst_reg()) && is_reg_dead(16, index))
	    {
	      log ("(e) %d: eliminate self load of %s\n", index, reg_names[ii.get_dst_regno ()]);
	      SET_INSN_DELETED(insn);
	      ++change_count;
	      continue;
	    }

	  if (ii.get_src_reg () && track->equals (ii.get_mode(), ii.get_src_regno (), SET_DEST(set)))
	    {
	      mask |= (1<<ii.get_dst_regno ());

	      log ("(e) %d: eliminate redundant reverse load to %s\n", index, reg_names[ii.get_dst_regno ()]);
	      SET_INSN_DELETED(insn);
	      ++change_count;
	      continue;
	    }

	  // is there a register holding that value?
	  if (!ii.get_src_reg ())
	    {
	      int aliasRegno = track->find_alias (src);
	      if (aliasRegno >= 0 && aliasRegno != ii.get_dst_regno ())
		{

		  if ( (mask & (1<<aliasRegno)))
		    continue;

		  mask |= (1<<ii.get_dst_regno ()) | (1<<aliasRegno);

		  log ("(e) %d: replace load with %s\n", index, reg_names[aliasRegno]);
		  validate_change (ii.get_insn (), &SET_SRC(set), gen_rtx_REG (ii.get_mode (), aliasRegno), 0);
		  ++change_count;
		}
	    }
	}
    }
  return change_count;
}

/*
 * Convert a series of move into absolute address into register based moves.
 */
static unsigned
opt_absolute (void)
{
  unsigned change_count = 0;

  for (unsigned i = 0; i < infos.size (); ++i)
    {
      insn_info & ii = infos[i];

      if (ii.is_compare ())
	continue;

      if (ii.get_src_op () && ii.is_src_ee () && !ii.get_src_intval ())
	continue;

      bool is_dst = ii.is_dst_mem () && (ii.has_dst_addr () || ii.get_dst_symbol ()) && !ii.has_dst_memreg ();
      bool is_src = ii.is_src_mem () && (ii.has_src_addr () || ii.get_src_symbol ()) && !ii.has_src_memreg ();

      if (!is_dst && !is_src)
	continue;

      if (ii.get_mode () == VOIDmode)
	continue;

      unsigned freemask = ~(ii.get_use () | ii.get_def ()) & 0x7f00 & usable_regs;
      if (!freemask)
	continue;

      rtx with_symbol = is_dst ? ii.get_dst_symbol () : ii.get_src_symbol ();

      std::vector<unsigned> found;
      found.push_back (i);
      int base = ii.get_dst_mem_addr ();
      int max = base;
      unsigned j = i + 1;
      for (; j < infos.size (); ++j)
	{
	  insn_info & jj = infos[j];
	  /* TODO: continue also at jump target */
	  if (jj.is_jump ())
	    continue;
	  /* TODO: check if label is visited only from jump targets from herein. then the label is ok. */
	  if (jj.is_label ())
	    break;

	  unsigned tempmask = freemask & ~(jj.get_use () | jj.get_def ());
	  if (!tempmask)
	    break;
	  freemask = tempmask;

	  if (jj.get_mode () == VOIDmode || jj.is_compare ())
	    continue;

	  if (jj.get_src_op () && jj.is_src_ee () && !jj.get_src_intval ())
	    continue;

	  bool j_dst = jj.is_dst_mem () && (jj.has_dst_addr () || jj.get_dst_symbol ()) && !jj.has_dst_memreg ()
	      && jj.get_dst_symbol () == with_symbol;
	  bool j_src = jj.is_src_mem () && (jj.has_src_addr () || jj.get_src_symbol ()) && !jj.has_src_memreg ()
	      && jj.get_src_symbol () == with_symbol;

	  /* exclude operations on that symbol. */

	  if (j_dst)
	    {
	      int addr = jj.get_dst_mem_addr ();
	      if (addr < base)
		{
		  if (max - addr <= 0x7ffe)
		    {
		      base = addr;
		      found.push_back (j);
		      continue;
		    }
		}
	      else if (addr - base <= 0x7ffe)
		{
		  if (addr > max)
		    max = addr;
		  found.push_back (j);
		  continue;
		}
	    }
	  if (j_src)
	    {
	      int addr = jj.get_src_mem_addr ();
	      if (addr < base)
		{
		  if (max - addr <= 0x7ffe)
		    {
		      base = addr;
		      found.push_back (j);
		      continue;
		    }
		}
	      else if (addr - base <= 0x7ffe)
		{
		  if (addr > max)
		    max = addr;
		  found.push_back (j);
		  continue;
		}
	    }
	}

      if (freemask && found.size () > 2)
	{
	  unsigned regno = bit2regno (freemask);
	  /* check again. */
	  for (std::vector<unsigned>::iterator k = found.begin (); k != found.end ();)
	    {
	      insn_info & kk = infos[*k];
	      bool k_dst = kk.is_dst_mem () && (kk.has_dst_addr () || kk.get_dst_symbol ()) && !kk.has_dst_memreg ()
		  && kk.get_dst_symbol () == with_symbol;
	      bool k_src = kk.is_src_mem () && (kk.has_src_addr () || kk.get_src_symbol ()) && !kk.has_src_memreg ()
		  && kk.get_src_symbol () == with_symbol;
	      if (k_dst && kk.get_dst_mem_addr () - base > 0x7ffc)
		k = found.erase (k);
	      else if (k_src && kk.get_src_mem_addr () - base > 0x7ffc)
		k = found.erase (k);
	      else if (insn_invalid_p (make_insn_raw (kk.make_absolute2base (regno, base, with_symbol, false)), 0))
		k = found.erase (k);
	      else
		++k;
	    }
	}
      if (freemask && found.size () > 2)
	{
	  unsigned regno = bit2regno (freemask);
	  if (with_symbol)
	    log ("(b) modifying %d symbol addresses for %s using %s\n", found.size (),
		 with_symbol->u.block_sym.fld[0].rt_str, reg_names[regno]);
	  else
	    log ("(b) modifying %d absolute addresses using %s\n", found.size (), reg_names[regno]);

	  unsigned current_use = ii.get_use ();

	  for (std::vector<unsigned>::iterator k = found.begin (); k != found.end (); ++k)
	    {
	      insn_info & kk = infos[*k];
	      kk.absolute2base (regno, base, with_symbol);
	      insn_invalid_p (kk.get_insn (), 0);
	    }

	  // load base into reg
	  rtx lea;

	  if (with_symbol)
	    {
	      if (base)
		lea = gen_rtx_SET(
		    gen_raw_REG (E_SImode, regno),
		    gen_rtx_CONST (E_SImode, gen_rtx_PLUS (E_SImode, with_symbol, gen_rtx_CONST_INT (E_SImode, base))));
	      else
		lea = gen_rtx_SET(gen_raw_REG (E_SImode, regno), with_symbol);
	    }
	  else
	    lea = gen_rtx_SET(gen_raw_REG (E_SImode, regno), gen_rtx_CONST_INT (E_SImode, base));
	  rtx_insn * insn = emit_insn_before (lea, ii.get_insn ());
	  insn_info nn (insn);
	  nn.set_use (current_use);
	  nn.scan ();
	  nn.fledder (lea);
	  nn.mark_def (regno);
	  infos.insert (infos.begin () + i, nn);

	  /* mark until last hit is found. */
	  for (unsigned k = i + 1; k < infos.size (); ++k)
	    {
	      infos[k].mark_use (regno);
	      if (k == *found.rbegin ())
		break;
	    }
	  ++change_count;
	  --i;
	}
    }

  if (change_count)
    update_insn2index ();

  return change_count;
}

static int
try_auto_inc (unsigned index, insn_info & ii, rtx reg)
{
  int const regno = REGNO(reg);
  rtx iiset = single_set(ii.get_insn());
  if (!iiset)
    return 0;

  // move.w (a0)+,a1 reads a word but writes a long...
  int size = GET_MODE_SIZE(ii.get_mode()).to_constant();
  if (reg == ii.get_src_mem_reg() && GET_CODE(SET_SRC(iiset)) == SIGN_EXTEND)
    size /= 2;
  if (size > 4)
    return 0;

//      log ("starting auto_inc search for %s at %d\n", reg_names[regno], index);

  // track all fixups to modify
  std::set<unsigned> fixups;

  // all paths to check
  std::vector<unsigned> todo;
  todo.push_back (index + 1);

  bool match_size = false;
  std::set<unsigned> visited;
  while (todo.size () > 0)
    {
      unsigned pos = todo[todo.size () - 1];
      todo.pop_back ();

      if (pos == index)
	return 0;

      if (visited.find (pos) != visited.end ())
	continue;
      visited.insert (pos);

      for (; pos < infos.size (); ++pos)
	{
	  insn_info & jj = infos[pos];

	  // do not auto_inc over calls for d0/d1/a0/a1/a7
	  if (jj.is_call() && ((1 << regno) & ( (1<<15)|(1<<9)|(1<<8)|(1<<1)|(1<<0) )) != 0)
	    return 0;

	  // check all jumps labels for register usage
	  if (jj.is_label ())
	    {
	      for (l2j_iterator j = label2jump.find (jj.get_insn ()->u2.insn_uid), k = j;
		  j != label2jump.end () && j->first == k->first; ++j)
		{
		  insn_info * ll = insn2info.find (j->second)->second;
		  if (ll->is_use (regno))
		    return 0;
		}
	      break;
	    }

	  // break if no longer used
	  if (!jj.is_use (regno))
	    break;

	  // abort if a parallel insn is touched.
	  if (GET_CODE(PATTERN(jj.get_insn())) == PARALLEL && (jj.is_def(regno) || jj.is_myuse(regno)))
	    return 0;

	  if (jj.in_proepi ())
	    return 0;

	  // add all labels
	  if (jj.is_jump ())
	    {
	      for (j2l_iterator j = jump2label.find (pos), k = j; j != jump2label.end () && j->first == k->first; ++j)
		todo.push_back (j->second);
	      continue;
	    }

	  // not used directly
	  if (!jj.is_myuse (regno))
	    continue;

	  // can't fixup such kind of insn (yet)
	  if (single_set (jj.get_insn ()) == 0)
	    return 0;

	  // if reg is src reg, op must be add and addend must be large enough
	  bool fix = false;
	  if (jj.get_src_mem_regno () == regno)
	    {
	      if (jj.get_dst_regno () == regno)
		return 0;

	      if (jj.get_src_mem_addr () < size)
		return 0;

	      if (jj.get_src_mem_addr () == size)
		match_size = true;

	      fix = true;
	    }
	  if (jj.get_dst_mem_regno () == regno)
	    {
	      if (jj.get_src_regno () == regno)
		return 0;

	      if (jj.get_dst_mem_addr () < size)
		return 0;

	      if (jj.get_dst_mem_addr () == size)
		match_size = true;

	      fix = true;
	    }

	  if (jj.get_src_regno() == jj.get_dst_regno() && jj.get_src_op() == PLUS && jj.get_src_intval() >= size)
	    fix = true;

	  if (!fix)
	    return 0;

	  fixups.insert (pos);

	  // done if this is an add
	  if (jj.is_def (regno))
	    break;
	}
    }

//  if (!match_size || !fixups.size ())
  if (!fixups.size ())
    return 0;

  if (!ii.make_post_inc (regno))
    return 0;

  log ("(i) auto_inc for %s at %d - %d fixups\n", reg_names[regno], index, fixups.size ());

  // fix all offsets / adds
  for (std::set<unsigned>::iterator k = fixups.begin (); k != fixups.end (); ++k)
    {
//	  log ("(i) fixup at %d\n", *k);
      insn_info & kk = infos[*k];
      kk.auto_inc_fixup (regno, size);
    }
  return 1;
}

/*
 * Convert a series of reg with offset ( (ax), 4(ax), 8(ax), ...) into autoincx ( (ax+), (ax+), (ax+), ...)
 *
 * 1. search a mem(reg) without offset and either src or dst is using that reg
 * 2. follow paths until reg is dead
 * 3. if there is another mem(reg) with offset check that
 *  a) offset fits last mode size
 *  b) all remaining insn using that reg can be updated by
 *    i) decrement the offset
 *    ii) decrement the add value
 */
static unsigned
opt_autoinc ()
{
  unsigned change_count = 0;

  update_label2jump ();

  for (unsigned index = 0; index < infos.size (); ++index)
    {
      insn_info & ii = infos[index];

      if (ii.in_proepi ())
	continue;

      if (!INSN_P(ii.get_insn ()))
	continue;

      if (GET_CODE(PATTERN(ii.get_insn())) == PARALLEL)
	continue;

      rtx set = single_set(ii.get_insn());
      if (!set)
	continue;


      if (MEM_P(SET_SRC(set)) && ii.get_src_mem_regno () >= 8 && !ii.get_src_mem_addr () && !ii.get_src_autoinc ()
	  && ii.get_src_mem_regno () != ii.get_dst_mem_regno () && ii.get_src_mem_regno () != ii.get_dst_regno ())
	change_count += try_auto_inc (index, ii, ii.get_src_mem_reg ());

      if (MEM_P(SET_DEST(set)) && ii.get_dst_mem_regno () >= 8 && !ii.get_dst_intval () && !ii.get_dst_autoinc ()
	  && ii.get_src_mem_regno () != ii.get_dst_mem_regno () && ii.get_src_regno () != ii.get_dst_mem_regno ())
	change_count += try_auto_inc (index, ii, ii.get_dst_mem_reg ());

    }

  return change_count;
}

/*
 * A final pass, with these optimizations:
 *
 * - convert cmp #0,ax int move.l ax,dy if there is a free dy
 */
static unsigned
opt_final()
{
  unsigned change_count = 0;
  for (unsigned index = 0; index < infos.size(); ++index)
    {
      insn_info &ii = infos[index];

      // cmp #0,ax
      if (ii.is_compare() && ii.get_dst_reg() && ii.get_dst_regno() >= 8 && ii.get_dst_regno() <= 15 && !ii.get_src_mem_reg() && ii.is_src_const() && ii.get_src_intval() == 0)
	{
	  // if there is a free dx register use a move
	  unsigned avail_dx = (usable_regs & ~ii.get_use()) & 0xff;
	  if (avail_dx)
	    {
	      unsigned regno = 0;
	      while ((avail_dx & 1) == 0)
		{
		  ++regno;
		  avail_dx >>= 1;
		}
	      rtx dx = gen_raw_REG(E_SImode, regno);
	      rtx ax = gen_raw_REG(E_SImode, ii.get_dst_regno());
	      rtx set = gen_rtx_SET(dx, ax);
	      emit_insn_before (set, ii.get_insn());


	      rtx cmp = gen_rtx_SET(cc0_rtx,
	      				gen_rtx_COMPARE (E_SImode, dx, gen_rtx_CONST_INT (E_SImode, 0)));
	      //rtx_insn * neu =
	      emit_insn_before (cmp, ii.get_insn());
	      SET_INSN_DELETED(ii.get_insn());

	      log ("(z) cmp.w #0,%s -> move.l %s,%s\n", reg_names[ii.get_dst_regno()], reg_names[ii.get_dst_regno()], reg_names[regno]);

	      ++ change_count;
	    }
	  continue;
	}

      // search moveq #0,dx
      if (ii.is_dst_reg() && ii.get_dst_regno() < 8 && index + 1 < infos.size())
	{
	  rtx set = single_set(ii.get_insn());
	  if (set)
	    {
	      rtx src = SET_SRC(set);
	      if (GET_CODE(src) == CONST_INT && INTVAL(src) == 0)
		{
		  // used in next insn as src and dead?
		  insn_info & jj = infos[index + 1];
		  rtx set1 = single_set(jj.get_insn());
		  if (set1 && jj.get_src_op() == 0 && !jj.is_compare() && !jj.get_multi_reg() && jj.get_src_reg() && jj.get_src_regno() == ii.get_dst_regno()
		      && is_reg_dead(ii.get_dst_regno(), index + 1))
		    {
		      if (validate_change(jj.get_insn(), &SET_SRC(set1), src, 0))
			{
			  SET_INSN_DELETED(ii.get_insn());
			  log("(z) %d: use clear instead of reg %s with #0\n", index, reg_names[jj.get_src_regno()]);
			  ++ change_count;
			}
		    }
		}
	    }
	}
    }
  return change_count;
}

/**
 * Convert
 *     lea <y>,ax
 *     move (ax),...
 * into
 *     move (<y>),...
 *
 *  if ax is reag dead
 */
static unsigned
opt_lea_mem()
{
  unsigned change_count = 0;
  for (unsigned index = 1; index< infos.size(); ++index)
    {
      insn_info &ii = infos[index - 1];

      if (!ii.get_dst_reg())
	continue;

      rtx set0 = single_set(ii.get_insn());
      if (!set0)
	continue;

      insn_info &jj = infos[index ];
      rtx set = single_set(jj.get_insn());
      if (!set)
	continue;

      rtx src = SET_SRC(set);
      if (!MEM_P(src))
	continue;

      rtx reg = XEXP(src, 0);
      if (!REG_P(reg))
	continue;

      if (REGNO(reg) != (unsigned)ii.get_dst_regno() || !is_reg_dead(REGNO(reg), index))
	continue;

      // try the conversion
      if (validate_change(jj.get_insn(), &XEXP(src, 0), SET_SRC(set0), 0))
	{
	  SET_INSN_DELETED(ii.get_insn());
	  log("(l) lea removed at %d\n", index - 1);
	  ++change_count;
	}
    }
  return change_count;
}


/**
 * Expand "clr mem" into "moveq #0,dx; move dx,mem", if possible.
 * Perform the cleanup in opt_final().
 */
static unsigned
opt_clear()
{
  unsigned change_count = 0;
  if (TUNE_68000)
  for (unsigned index = 0; index< infos.size(); ++index)
    {
      insn_info &ii = infos[index];

      if (GET_MODE_SIZE(ii.get_mode()).to_constant() > 4)
	continue;

      rtx set0 = single_set(ii.get_insn());
      if (!set0)
	continue;

      rtx src = SET_SRC(set0);
      if (GET_CODE(src) != CONST_INT || INTVAL(src))
	continue;

      if (!MEM_P(SET_DEST(set0)))
	continue;

      unsigned regs = ~ii.get_use() & usable_regs & 0xff;
      if (!regs)
	continue;

      unsigned regno = 0;
      while (!(regs & 1))
	{
	  ++regno;
	  regs >>= 1;
	}

      if (validate_change(ii.get_insn(), &SET_SRC(set0), gen_rtx_REG(GET_MODE(SET_DEST(set0)), regno), 0))
	{
	  rtx set = gen_rtx_SET(gen_rtx_REG(E_SImode, regno), gen_rtx_CONST_INT(E_SImode, 0));
	  emit_insn_before (set, ii.get_insn());
	  ++change_count;

	  log("(z) %d: use reg %s with #0 instead of clear\n", index, reg_names[regno]);
	}
    }
  return change_count;
}

/**
 * Exchange insns if dst operand of an insn is used in the next insn as src operand.
 */
static void
opt_pipeline_insns()
{
  // up
  for (unsigned index = 1; index < infos.size() - 1; ++index)
    {
      insn_info & ii = infos[index];

      // only check if not in prolog and a register is set
      rtx iiset = single_set(ii.get_insn());
      if (ii.in_proepi() || ii.is_compare() || !ii.get_dst_reg() || ii.get_hard() || !iiset)
	continue;

      insn_info & jj = infos[index + 1];
      // don't touch compares and check for register overlap
      if (jj.is_compare() || !(jj.get_myuse() & ii.get_def()))
	continue;

      // check previous insn
      insn_info & hh = infos[index - 1];
      rtx hhset = single_set(hh.get_insn());
      if (hh.is_call() || hh.is_label() || hh.is_jump() || hh.in_proepi() || hh.is_compare() || hh.get_hard() || !hhset || !hh.get_dst_reg())
	continue;

      // overlap with current insn
      if (((ii.get_myuse() | ii.get_def()) & hh.get_def() & ~(1<<FIRST_PSEUDO_REGISTER)) != 0 || (hh.get_myuse() & ii.get_def()) != 0 || rtx_equal_p(SET_SRC(iiset), SET_DEST(hhset)))
	continue;

      rtx pat = PATTERN(hh.get_insn());

      // don't move volatil insns
      if (pat->volatil)
	continue;

//      fprintf(stderr, "reorder insns: ");
//      debug_rtx(hh.get_insn());
//      debug_rtx(ii.get_insn());

      // swap da insns
      rtx_insn * head = PREV_INSN(hh.get_insn());
      rtx_insn * tail = NEXT_INSN(ii.get_insn());

      SET_NEXT_INSN(head) = ii.get_insn();
      SET_NEXT_INSN(ii.get_insn()) = hh.get_insn();
      SET_NEXT_INSN(hh.get_insn()) = tail;

      SET_PREV_INSN(tail) = hh.get_insn();
      SET_PREV_INSN(hh.get_insn()) = ii.get_insn();
      SET_PREV_INSN(ii.get_insn()) = head;

      std::swap(infos[index], infos[index - 1]);
      log("(n) reordered insn %d<->%d\n", index - 1, index);
    }
}


void print_inline_info()
{
  unsigned count = 0;
  for (unsigned index = 0; index < infos.size(); ++index)
    {
      if (!infos[index].in_proepi())
	++count;
    }

  for (unsigned m = usable_regs >> 2; m; m>>=1)
    {
      if (count && (m&1))
	--count;
    }

  printf(":bbb: inline weight = %4d\t%s\n", count, get_current_function_name ());
}

namespace
{

  const pass_data pass_data_bbb_optimizations =
    { RTL_PASS, /* type */
    "bebbo's-optimizers", /* name */
    OPTGROUP_NONE, /* optinfo_flags */
    TV_NONE, /* tv_id */
    0, /* properties_required */
    0, /* properties_provided */
    0, /* properties_destroyed */
    0, /* todo_flags_start */
    0, //( TODO_df_finish | TODO_df_verify), /* todo_flags_finish */
      };

  class pass_bbb_optimizations : public rtl_opt_pass
  {
  public:
    pass_bbb_optimizations (gcc::context *ctxt) :
	rtl_opt_pass (pass_data_bbb_optimizations, ctxt), pp (0)
    {
    }

    /* opt_pass methods: */
    virtual bool
    gate (function * fun)
    {
  	  ::optimize_this_for_speed_p = optimize_function_for_speed_p (fun);

      if (!string_bbb_opts)
	string_bbb_opts = "+";

      return TARGET_AMIGA && optimize > 0 && string_bbb_opts && !strchr (string_bbb_opts, '-');
    }

    virtual unsigned int
    execute (function *)
    {
      return execute_bbb_optimizations ();
    }

    opt_pass *
    clone ()
    {
      pass_bbb_optimizations * bbb = new pass_bbb_optimizations (m_ctxt);
      bbb->pp = pp + 1;
      return bbb;
    }

    unsigned int pp;

    unsigned
    execute_bbb_optimizations (void);
  };
// class pass_bbb_optimizations

  /* Main entry point to the pass.  */
  unsigned
  pass_bbb_optimizations::execute_bbb_optimizations (void)
  {
    int done;
    dump_cycles = strchr (string_bbb_opts, 'C') != 0;
    dump_reg_track = strchr (string_bbb_opts, 'R') != 0;
    be_very_verbose = strchr (string_bbb_opts, 'V') != 0;
    be_verbose = strchr (string_bbb_opts, 'v') != 0;
    if (be_verbose && be_very_verbose)
      ++be_very_verbose;
    if (be_very_verbose)
      be_verbose = true;

    bool do_commute_add_move = strchr (string_bbb_opts, 'a') || strchr (string_bbb_opts, '+');
    bool do_absolute = strchr (string_bbb_opts, 'b') || strchr (string_bbb_opts, '+');
    bool do_const_cmp_to_sub = strchr (string_bbb_opts, 'c') || strchr (string_bbb_opts, '+');
    bool do_elim_dead_assign = strchr (string_bbb_opts, 'e') || strchr (string_bbb_opts, '+');
    bool do_shrink_stack_frame = strchr (string_bbb_opts, 'f') || strchr (string_bbb_opts, '+');
    bool do_autoinc = strchr (string_bbb_opts, 'i') || strchr (string_bbb_opts, '+');
    bool do_lea_mem = strchr (string_bbb_opts, 'l') || strchr (string_bbb_opts, '+');
    bool do_merge_add = strchr (string_bbb_opts, 'm') || strchr (string_bbb_opts, '+');
    bool do_pipeline = strchr (string_bbb_opts, 'n') || strchr (string_bbb_opts, '+');
    bool do_propagate_moves = strchr (string_bbb_opts, 'p') || strchr (string_bbb_opts, '+');
    bool do_bb_reg_rename = strchr (string_bbb_opts, 'r') || strchr (string_bbb_opts, '+');
    bool do_opt_strcpy = strchr (string_bbb_opts, 's') || strchr (string_bbb_opts, '+');
    bool do_opt_final = strchr (string_bbb_opts, 'z') || strchr (string_bbb_opts, '+');

    if (be_very_verbose)
      log ("ENTER\n");

    unsigned r = update_insns ();
    if (!r)
      {
	if (do_lea_mem && opt_lea_mem())
	  update_insns ();

	if (do_opt_final && opt_clear())
	  update_insns ();

	int pass = 0;
	for (;;)
	  {
	    done = 1;
	    if (be_very_verbose)
	      log ("pass %d\n", ++pass);
	    if (do_opt_strcpy && opt_strcpy ())
	      {XUSE('s'); done = 0; update_insns (); }

	    if (do_commute_add_move && opt_commute_add_move ())
	      {XUSE('a'); done = 0; update_insns (); }

	    if (do_propagate_moves && opt_propagate_moves ())
	      {XUSE('p'); done = 0; update_insns (); }

	    if (do_const_cmp_to_sub && opt_const_cmp_to_sub ())
	      {XUSE('c'); done = 0; update_insns (); }

	    if (do_merge_add && opt_merge_add ())
	      {XUSE('m'); done = 0; update_insns(); }

	    if (do_absolute && opt_absolute ())
	      {XUSE('b'); done = 0; update_insns (); }

	    if (do_autoinc && opt_autoinc ())
	      {XUSE('i'); done = 0; update_insns (); }

	    if (do_bb_reg_rename)
	      while (opt_reg_rename ())
		{
		  XUSE('r');
		  update_insns ();
		  done = 0;
		}

	    if (do_elim_dead_assign) while(opt_elim_dead_assign (STACK_POINTER_REGNUM))
	      {
		XUSE('e');
		done = 0;
		update_insns ();
	      }

	    if (done)
	      break;
	  }

	/* convert back to clear befor fixing the stack frame */
	if (do_opt_final && opt_final())
	  { XUSE('z'); update_insns(); }

	if (do_shrink_stack_frame && opt_shrink_stack_frame ())
	  { XUSE('f'); update_insns (); }

	/* elim assignments to the stack pointer last. */
	if (do_elim_dead_assign && opt_elim_dead_assign (FIRST_PSEUDO_REGISTER))
	  { XUSE('e'); update_insns (); }

	if (do_pipeline)
	  opt_pipeline_insns ();
      }
    if (r && be_verbose)
      log ("no bbb optimization code %d\n", r);

    if (strchr (string_bbb_opts, 'X') || strchr (string_bbb_opts, 'x'))
      dump_insns ("bbb", strchr (string_bbb_opts, 'X'));

    if (dump_reg_track || dump_cycles || be_very_verbose)
      {
	update_insns ();
	if (dump_reg_track)
	  track_regs ();
      }

    if (be_verbose)
      print_inline_info();

    XUSE('\n');
    return r;
  }

}      // anon namespace

rtl_opt_pass *
make_pass_bbb_optimizations (gcc::context * ctxt)
{
  return new pass_bbb_optimizations (ctxt);
}
namespace
{

  const pass_data pass_data_bbb_baserel =
    { RTL_PASS, /* type */
    "bebbo's-baserel-pass", /* name */
    OPTGROUP_NONE, /* optinfo_flags */
    TV_NONE, /* tv_id */
    0, /* properties_required */
    0, /* properties_provided */
    0, /* properties_destroyed */
    0, /* todo_flags_start */
    0, //( TODO_df_finish | TODO_df_verify), /* todo_flags_finish */
      };

  class pass_bbb_baserel : public rtl_opt_pass
  {
  public:
    pass_bbb_baserel (gcc::context *ctxt) :
	rtl_opt_pass (pass_data_bbb_baserel, ctxt), pp (0)
    {
    }

    /* opt_pass methods: */
    virtual bool
    gate (function *)
    {
      return TARGET_AMIGA && flag_pic >= 3;
    }

    virtual unsigned int
    execute (function *)
    {
      return execute_bbb_baserel ();
    }

    opt_pass *
    clone ()
    {
      pass_bbb_baserel * bbb = new pass_bbb_baserel (m_ctxt);
      return bbb;
    }

    unsigned int pp;

    unsigned
    execute_bbb_baserel (void);
  };
// class pass_bbb_optimizations

  static rtx a4reg;
  static int cur_tmp_use;
  static rtx cur_symbol[8];
  static rtx cur_tmp_reg[8];

  int make_pic_ref(rtx_insn * insn, rtx * x, bool * use_tmp)
  {
    int r = 0;
    enum rtx_code code = GET_CODE(*x);
    if (code == SYMBOL_REF)
      {
	bool ispic = false;
	section * sec = 0;

	tree decl = SYMBOL_REF_DECL (*x);
	if (decl &&  (decl->base.code == VAR_DECL || decl->base.code == CONST_DECL) && !(DECL_SECTION_NAME(decl)))
	  {
	    sec = get_variable_section(decl, false);
	    ispic = (sec->common.flags & 0x200) && !decl->base.readonly_flag; // SECTION_WRITE;
	  }

//	  if (decl)
//	    printf("%s: %8x %d\n", decl->decl_minimal.name->identifier.id.str, sec ? sec->common.flags : 0, ispic);

	if (ispic)
	  {
	    rtx symbol = *x;

	    // create the pic_ref expression
	    rtx s = gen_rtx_UNSPEC (Pmode, gen_rtvec (2, *x, GEN_INT (0)),
						UNSPEC_RELOC16);
	    s = gen_rtx_CONST (Pmode, s);
	    s = gen_rtx_PLUS (Pmode, a4reg, s);
	    s = gen_rtx_CONST (Pmode, s);

	    // try to use it directly.
	    if (!use_tmp)
	      validate_unshare_change(insn, x, s, 0);
	    else if (!*use_tmp)
	      *use_tmp |= !validate_unshare_change(insn, x, s, 0);

	    // if direct use failed, use a tmp register per symbol
	    if (use_tmp && *use_tmp)
	      {
		rtx r = 0;
		for (int i = 0; i < cur_tmp_use; ++i)
		  {
		    if (rtx_equal_p(cur_symbol[i], symbol))
		      {
		        r = cur_tmp_reg[i];
			break;
		      }
		  }
		if (!r)
		  {
		    r = gen_reg_rtx (Pmode);
		    rtx set = gen_rtx_SET(r, s);
		    emit_insn_before(set, insn);

		    cur_symbol[cur_tmp_use] = symbol;
		    cur_tmp_reg[cur_tmp_use] = r;
		    ++cur_tmp_use;
		  }

		// if the change does not validate, poke it hard and pray that it's fixed later on. see maybe_fix()
		if (!validate_unshare_change(insn, x, r, 0))
		  {
//		    fprintf(stderr, "can't convert to baserel: ");
//		    debug_rtx(insn);
		    *x = r;
//		    debug_rtx(insn);
		    return -1;
		  }
	      }
	  }

	return ispic;
      }

    switch (code)
    {
      /*
       * Handle set: SRC and DEST may each have different symbols, so reset the use_tmp flag.
       */
      case SET:
	r |= make_pic_ref(insn, &SET_DEST(*x), use_tmp);
	if (use_tmp)
	  *use_tmp = false;
	r |= make_pic_ref(insn, &SET_SRC(*x), use_tmp);
	if (use_tmp)
	  *use_tmp = false;
	return r;
	/*
	 * No inplace pic ref if a register is seen
	 */
      case REG:
	if (use_tmp)
	  *use_tmp = true;
	break;
	/*
	 * There are shared CONST(PLUS(SYMBOL, CONST_INT)) rtx! (evil!)
	 * Make a copy if one is seen, to avoid double replacement.
	 */
      case CONST:
	if (GET_CODE(XEXP(*x, 0)) == PLUS && GET_CODE(XEXP(XEXP(*x, 0), 0)) == SYMBOL_REF)
	  {
	    /* copy_rtx can't unshare, so do it by hand. */
	    rtx c = gen_rtx_CONST(GET_MODE(*x), gen_rtx_PLUS(GET_MODE(XEXP(*x, 0)), XEXP(XEXP(*x, 0), 0), XEXP(XEXP(*x, 0), 1)));
	    *x = c;

	    if (!make_pic_ref(insn, &XEXP(*x, 0), use_tmp))
	      return 0;

	    // remove CONST
	    *x = XEXP(*x, 0);

	    return 1;
	  }
	break;
	/*
	 * Default: try in place first.
	 */
      default:
	break;
    }

    const char *fmt = GET_RTX_FORMAT(code);
    for (int i = GET_RTX_LENGTH (code) - 1; i >= 0; i--)
      {
        if (fmt[i] == 'e')
  	{
  	  r |= make_pic_ref(insn, &XEXP(*x, i), use_tmp);
  	}
        else if (fmt[i] == 'E')
  	for (int j = XVECLEN (*x, i) - 1; j >= 0; j--)
  	  {
  	    r |= make_pic_ref(insn, &XVECEXP(*x, i, j), use_tmp);
  	  }
      }
    return r;
  }

  void
  maybe_fix(rtx x, rtx_insn * insn)
  {
    /* check for necessary fixes
     * 1. (mem/f:SI (plus:SI (reg:SI 8 a0)
     *       (const:SI (plus:SI (reg:SI 0 d0 [96])
     *         (const_int 8 [0x8]))))
     *
     *   (mem:SI (plus:SI (plus:SI (reg/v:SI 8 a0)
     *                             (reg:SI 0 d0))
     *         (const_int 8 [0x8])))
     *
     *
     *
     * 2. not converted properly
     * (mem:SI (plus:SI (mult:SI (reg:SI 31 )
     *                           (const_int 8 [0x8]))
     *                  (const:SI (plus:SI (reg:SI 99 )
     *                                     (const_int 4 [0x4]))))
     *
     *
     * 3. (mem:SI (plus:SI (plus:SI (reg:SI 35 [ _23 ])
     *                              (reg:SI 31 [ ivtmp.233 ]))
     *                     (reg:SI 46)) )
     *
     * 3 registers are too many.
     *
     * 4. (mem/f:SI (plus:SI (plus:SI (mult:SI (reg:SI 1 d1)
     *                                         (const_int 4 [0x4]))
     *                                (reg:SI 14 a6))
     *                       (const:SI (plus:SI (reg:SI 0 d0 [1060])
     *                                          (const_int 8 [0x8]))))
     *
     * again 3 registers.
     * Also move the const/plus/reg into a separate register.
     *
     */

    /* MEM can be nested inside. */
    if (GET_CODE(x) == ZERO_EXTEND || GET_CODE(x) == SIGN_EXTEND || GET_CODE(x) == STRICT_LOW_PART)
      x = XEXP(x, 0);

    if (MEM_P(x))
      {
	rtx plus = XEXP(x, 0);
	if (GET_CODE(plus) == CONST)
	  plus = XEXP(plus, 0);

	// it's really a PLUS
	if (GET_CODE(plus) == PLUS)
	  {
	    rtx op0 = XEXP(plus, 0);
	    if (GET_CODE(op0) == CONST)
	      op0 = XEXP(op0, 0);
	    rtx op1 = XEXP(plus, 1);
	    if (GET_CODE(op1) == CONST)
	      op1 = XEXP(op1, 0);

	    // set to MEM - not null
	    rtx op00 = x;
	    rtx op01 = x;
	    rtx op10 = x;
	    rtx op11 = x;
	    if (GET_CODE(op0) == PLUS)
	      {
		op00 = XEXP(op0, 0);
		op01 = XEXP(op0, 1);
	      }
	    if (GET_CODE(op1) == PLUS)
	      {
		op10 = XEXP(op1, 0);
		op11 = XEXP(op1, 1);
	      }
	    if (GET_CODE(op00) == MULT)
	      op00 = XEXP(op00, 0);

	    int regCount0 = REG_P(op00) + REG_P(op01) + REG_P(op0);
	    int regCount1 = REG_P(op10) + REG_P(op11) + REG_P(op1);

	    // patch needed if too many registers
	    if (regCount0 + regCount1 <= 2)
	      return;

	    // use a temp register for op0
	    if (regCount0 == 2)
	      {
		rtx t0 = gen_reg_rtx (Pmode);
		rtx set = gen_rtx_SET(t0, XEXP(plus, 0));
		emit_insn_before(set, insn);

		validate_change(insn, &XEXP(plus, 0), t0, 0);
	      }
	    // use a temp register for op1
	    if (regCount1 == 2)
	      {
		rtx t1 = gen_reg_rtx (Pmode);
		rtx set = gen_rtx_SET(t1, XEXP(plus, 1));
		emit_insn_before(set, insn);

		validate_change(insn, &XEXP(plus, 1), t1, 0);
	      }
	  }

#if 0
	// CONST(PLUS(...)) -> PLUS(...)
	if (GET_CODE(plus) == CONST && GET_CODE(XEXP(plus, 0)) == PLUS)
	  {
	    validate_change (insn, &XEXP(x, 0), XEXP(plus, 0), 0);
	    plus = XEXP(x, 0);
	  }

	// it's really a PLUS
	if (GET_CODE(plus) == PLUS)
	  {
	    rtx op10 = XEXP(plus, 0);
	    rtx op11 = XEXP(plus, 1);

	    if (GET_CODE(op10) == PLUS)
	      {
		// DROP CONST from inner PLUS
		if (GET_CODE(op11) == CONST && GET_CODE(XEXP(op11, 0)) == PLUS)
		  {
		    rtx plus2 = XEXP(op11, 0);
		    rtx op20 = XEXP(plus2, 0);
		    rtx op21 = XEXP(plus2, 1);

		    rtx p2 = gen_rtx_PLUS(GET_MODE(plus2), op20, op21);
		    rtx p1 = gen_rtx_PLUS(GET_MODE(plus2), op10, p2);

		    // replace plus
		    validate_change(insn, &XEXP(x, 0), p1, 0);

		    // update variables
		    plus = XEXP(x, 0);
		    op10 = XEXP(plus, 0);
		    op11 = XEXP(plus1, 1);
		  }
	      }

	    // is 2nd operator also a plus?
	    while ((GET_CODE(op11) == PLUS) && (GET_CODE(op10) == PLUS && (REG_P(XEXP(op10, 0)) || GET_CODE(XEXP(op10, 0)) == MULT) && REG_P(XEXP(op10, 1))))
	      {
		// create an additional add insn for pl2
		rtx r = gen_reg_rtx (Pmode);
		rtx set = gen_rtx_SET(r, op10);
		emit_insn_before(set, insn);

		// use that register instead of op10
		validate_change(insn, &XEXP(plus, 0), r, 0);

		if ((GET_CODE(XEXP(plus, 1)) == CONST && GET_CODE(XEXP(XEXP(plus1, 1), 0)) == PLUS))
		  {
		    rtx r2 = gen_reg_rtx (Pmode);
		    rtx set2 = gen_rtx_SET(r2, XEXP(XEXP(plus, 1), 0));
		    emit_insn_before(set2, insn);

		    validate_change(insn, &XEXP(plus, 1), r2, 0);
		  }

		// update variables
		plus = XEXP(x, 0);
		op10 = XEXP(plus, 0);
		op11 = XEXP(plus, 1);

	      }
	  }
#endif
      }
  }

  /* Main entry point to the pass.  */
  unsigned
  pass_bbb_baserel::execute_bbb_baserel (void)
  {
    a4reg = gen_rtx_REG (Pmode, PIC_REG);

    rtx_insn *insn, *next;
    for (insn = get_insns (); insn; insn = next)
      {
	next = NEXT_INSN (insn);

	if (NONJUMP_INSN_P(insn))
	  {

	    rtx set = single_set (insn);
	    bool b = false;
	    cur_tmp_use = 0;
	    if (make_pic_ref(insn, &PATTERN(insn), &b) && set)
	      {
//		rtx_insn * new_insn = make_insn_raw (PATTERN(insn));
//		if (insn_invalid_p(new_insn, 0))
		  {
		    /* some insns need a further patch to be valid.
		     * See maybe_fix.
		     */
		    rtx dest = SET_DEST(set);
		    rtx src = SET_SRC(set);

		    if (GET_CODE(src) == COMPARE)
		      {
			dest = XEXP(src, 0);
			src = XEXP(src, 1);
		      }

		    maybe_fix(dest, insn);
		    maybe_fix(src, insn);
		  }
	      }

	    rtx note = find_reg_note (insn, REG_EQUAL, NULL_RTX);
	    if (note)
	      {
		make_pic_ref(insn, &XEXP (note, 0), 0);
	      }
	  }
      }

    return 0;
  }

}      // anon namespace

rtl_opt_pass *
make_pass_bbb_baserel (gcc::context * ctxt)
{
  return new pass_bbb_baserel (ctxt);
}
