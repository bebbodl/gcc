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
#include "tm_p.h"
#include "insn-config.h"
#include "recog.h"
#include "cfgrtl.h"
#include "emit-rtl.h"
#include "tree.h"
#include "tree-pass.h"
#include "conditions.h"
#include "langhooks.h"
#include "output.h"
#include <vector>
#include <set>
#include <map>
#include <genrtl.h>

//#define XUSE(c) fputc(c, stderr)
#define XUSE(c)

int be_very_verbose;
bool be_verbose;
static int pass;

bool optimize_this_for_speed_p;
extern bool
optimize_function_for_speed_p (struct function *fun);

extern struct lang_hooks lang_hooks;

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
  unsigned used[FIRST_PSEUDO_REGISTER];

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
	if (GET_MODE_SIZE(dstMode) != 4)
	  return false;
	/* these can be used directly. */
	*z = x;
	return true;

      case REG:
	{
	  /* store the reg. */
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
	  // cache restict and stack spills
	  if (MEM_IN_STRUCT_P(x) || MEM_READONLY_P(x))
	    {
	      *z = x;
	      return true;
	    }
	  return false;
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
	  used[i] = 0;
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
  invalidate_mem (rtx mem, unsigned index)
  {
    rtx z = 0;
    if (extend (&z, GET_MODE(mem), mem))
      {
	rtx reg = 0;
	int iv = 0;
	if (MEM_IN_STRUCT_P(mem))
	  {
	    rtx x = XEXP(mem, 0);
	    if (GET_CODE(x) == PLUS || GET_CODE(x) == MINUS)
	      {
		rtx creg = XEXP(x, 0);
		rtx cint = XEXP(x, 1);
		if (REG_P(creg) && CONST_INT_P(cint))
		  {
		    reg = creg;
		    iv = (int) INTVAL(cint);
		  }
	      }
	  }

	if (iv) for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
	  {
	    if (rtx_equal_p (z, value[i]))
	      {
		clear(SImode, i, index);
		continue;
	      }
	    // check for subreg/strict_low: overlap +/-3 -> clear the cache
	    rtx mem = value[i];
	    if (reg && mem && MEM_P(mem) && MEM_IN_STRUCT_P(mem))
	      {
		rtx pl = XEXP(mem, 0);
		if (GET_CODE (pl) == PLUS || GET_CODE (pl) == MINUS)
		  {
		    rtx r = XEXP(pl, 0);
		    rtx v = XEXP(pl, 1);
		    if (rtx_equal_p (r, reg) && CONST_INT_P(v)
			&& (INTVAL(v) + 3 <= iv || INTVAL(v) - 3 >= iv))
		      {
			clear(SImode, i, index);
		      }
		  }
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
  set (machine_mode mode, unsigned regno, rtx src, unsigned usedhere, unsigned index)
  {
    if (regno >= FIRST_PSEUDO_REGISTER)
      return;

    if (mode == DImode && GET_CODE(src) == CONST_INT)
      {
	rtx hi = gen_rtx_CONST_INT(VOIDmode, INTVAL(src) >> 32);
	rtx lo = gen_rtx_CONST_INT(VOIDmode, INTVAL(src) & 0xffffffff);
	set(SImode, regno, hi, usedhere, index);
	set(SImode, regno + 1, lo, usedhere, index);
	return;
      }

    if (mode == SFmode && regno < 16)
      mode = SImode;

    if (GET_CODE(src) == CONST_INT && (mode == HImode || mode == QImode))
      {
	unsigned iv = UINTVAL(src);
	setMask(regno, iv, mode);
	value[regno] = gen_rtx_CONST_INT(mode, 0x100000000000000LL | ((long long int ) (regno) << 32) | index);
	used[regno] = 1 << FIRST_PSEUDO_REGISTER;
	clearRefsByMask(1<<regno, index);
      }
    else if (extend (&value[regno], mode, src))
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

	used[regno] = usedhere;
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
	    used[regno] = used[refregno];
	  }

	clearRefsByMask(1<<regno, index);
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
    if (GET_MODE_SIZE(mode) == 1)
      andMask[regno] = (andMask[regno] & 0xffffff00) | (mask & 0xff);
    else
    if (GET_MODE_SIZE(mode) == 2)
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
    if (REG_P(x) && REGNO(x) < 16 && xmode == SFmode)
      xmode = SImode;

    if (mode == SFmode && regno < 16)
      mode = SImode;

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

    if (mode == SFmode && regno < 16)
      mode = SImode;
    value[regno] = gen_rtx_CONST_INT(mode, 0x100000000000000LL | ((long long int ) (regno) << 32) | index);
    used[regno] = 1 << FIRST_PSEUDO_REGISTER;
    setMask(regno, 0xffffffff, mode);

    clearRefsByMask(1 << regno, index);
  }

  void
  clearRefsByMask(unsigned mask, unsigned index) {
    // clear also all using this register.
    for (int i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (used[i] & mask) {
	    clear(SImode, i, index);
	}
      }
  }

  void
  clear_aftercall (unsigned index)
  {
    for (int i = 2; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (value[i] && MEM_P(value[i]))
	  {
	    value[i] = 0;
	    used[i] = 0;
	    andMask[i] = 0xffffffff;
	  }
      }
    clear (SImode, 0, index);
    clear (SImode, 1, index);
    clear (SImode, 8, index);
    clear (SImode, 9, index);
    clear (SImode, 16, index);
    clear (SImode, 17, index);
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
	  clear (SImode, regno, index);
      }
  }

  void
  assign (track_var const * o)
  {
    for (int i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	value[i] = o->value[i];
	used[i] = o->used[i];
	andMask[i] = o->andMask[i];
      }
  }

  /* only keep common values in both sides. */
  void
  merge (track_var * o)
  {
    for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
      {
	if (!rtx_equal_p (value[i], o->value[i]))
	  {
	    value[i] = o->value[i] = 0;
	    used[i] = 0;
	    andMask[i] = 0xffffffff; // don't want to - but without loop detection
	                             // this might lead to a elimination of
	                             // a possible merge source...
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

// usage flags - 32 sets also 16,8; 16 sets also 8.
  unsigned myuse8, myuse16, myuse32;  // bit set if registers are used in this statement
  unsigned use8, use16, use32;        // bit set if registers are used in program flow
  unsigned def8, def16, def32;        // bit set if registers are defined here

  unsigned hard; // bit set if registers can't be renamed

  enum proepis proepi;

  bool stack; // part of stack frame insns

// stuff to analyze insns
  bool label;
  bool jump;
  bool call;
  bool compare;
  bool dst_mem;
  bool src_mem;
  bool src_plus;
  int src_intval;
  rtx_code src_op;
  bool src_ee;
  bool src_2nd;
  bool src_const;

  machine_mode mode;

  rtx dst_reg;
  rtx src_reg;

  struct m68k_address src_addr;
  int src_mem_addr;
  struct m68k_address dst_addr;
  int dst_mem_addr;

  bool visited;

  int sp_offset;

  int dst_autoinc;
  int src_autoinc;

  unsigned multi_reg; /* bit field for register pairs. */

// values for all variables - if used
  track_var * track;

public:
  insn_info (rtx_insn * i = 0, enum proepis p = IN_CODE) :
      insn (i), myuse8 (0), myuse16 (0), myuse32 (0),
      use8 (0), use16(0), use32(0),
      def8 (0), def16(0), def32(0),
      hard (0), proepi (p), stack (false), label (false), jump (false), call (false), compare (false), dst_mem (false), src_mem (false),
      src_plus (false), src_intval(0), src_op ((rtx_code) 0),  src_ee (false), src_2nd (false), src_const (false), mode (VOIDmode),
      dst_reg (0), src_reg (0), src_mem_addr(0), dst_mem_addr(0), visited (false), sp_offset (0), dst_autoinc (0), src_autoinc (0), multi_reg(0), track (0)
  {
    memset(&src_addr, 0, sizeof(src_addr));
    memset(&dst_addr, 0, sizeof(dst_addr));
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
    return dst_addr.base_loc || dst_addr.index_loc;
  }

  inline bool
  has_src_memreg () const
  {
    return src_addr.base_loc || src_addr.index_loc;
  }

  inline rtx_code
  get_src_mem_mem () const
  {
    return (rtx_code)src_addr.code;
  }

  inline rtx_code
  get_dst_mem_mem () const
  {
    return (rtx_code)dst_addr.code;
  }

  inline rtx
  get_dst_symbol () const
  {
    return dst_addr.offset;
  }

  inline rtx
  get_src_symbol () const
  {
    return src_addr.offset;
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

  inline int
  get_dst_mem_addr () const
  {
    return dst_mem_addr;
  }

  inline int
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
    return src_addr.base_loc ? REGNO (*src_addr.base_loc): -1;
  }

  inline int
  get_src_mem2_regno () const
  {
    return src_addr.index_loc ? REGNO (*src_addr.index_loc): -1;
  }

  inline int
  get_dst_mem_regno () const
  {
    return dst_addr.base_loc ? REGNO (*dst_addr.base_loc): -1;
  }

  inline int
  get_dst_mem2_regno () const
  {
    return dst_addr.index_loc ? REGNO (*dst_addr.index_loc): -1;
  }

  inline rtx
  get_src_mem_reg () const
  {
    return src_addr.base_loc ? *src_addr.base_loc: 0;
  }

  inline rtx
  get_src_mem2_reg () const
  {
    return src_addr.index_loc ? *src_addr.index_loc: 0;
  }

  inline rtx
  get_dst_mem_reg () const
  {
    return dst_addr.base_loc ? *dst_addr.base_loc: 0;
  }

  inline rtx
  get_dst_mem2_reg () const
  {
    return dst_addr.index_loc ? *dst_addr.index_loc: 0;
  }

  inline int
  get_src_intval () const
  {
    return src_intval;
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

  void
  fledder_dst_mem (rtx src);

  /* update usage. */
  void
  update (insn_info & o)
  {
    myuse8 = o.myuse8;
    myuse16 = o.myuse16;
    myuse32 = o.myuse32;
    use8 = o.use8;
    use16 = o.use16;
    use32 = o.use32;
    def8 = o.def8;
    def16 = o.def16;
    def32 = o.def32;
    hard = o.hard;
    multi_reg = o.multi_reg;
  }

  inline void
  reset_use ()
  {
    visited = false;
    use8 = use16 = use32 = 0;
    def8 = def16 = def32 = 0;
    myuse8 = myuse16 = myuse32 = 0;
    hard = 0;
    multi_reg = 0;
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
    src_plus = false;
    src_op = (rtx_code) 0;
    src_ee = false;
    src_const = false;

    mode = VOIDmode;

    dst_reg = 0;
    src_reg = 0;

    src_intval = 0;

    dst_autoinc = 0;
    src_autoinc = 0;

    memset(&src_addr, 0, sizeof(src_addr));
    memset(&dst_addr, 0, sizeof(dst_addr));
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
    return !def8 && !use8 && !hard;
  }

  /** mark usage here as 32 bit. */
  inline void
  mark_myuse (int regno, int sz)
  {
    myuse8 |= 1 << regno;
    use8 |= 1 << regno;
    if (sz > 1)
      {
	myuse16 |= 1 << regno;
	use16 |= 1 << regno;
	if (sz > 2)
	  {
	    myuse32 |= 1 << regno;
	    use32 |= 1 << regno;
	  }
      }
  }

  /** mark usage here as 32 bit. */
  inline void
  mark_myuse (rtx reg)
  {
    int regno = REGNO(reg);
    int sz = GET_MODE_SIZE(GET_MODE(reg));
    mark_myuse(regno, sz);
  }

  /** mark usage as 32 bit. */
  inline void
  mark_use (int regno)
  {
    use8 |= 1 << regno;
    use16 |= 1 << regno;
    use32 |= 1 << regno;
  }

  /** mark def as 32 bit. */
  inline void
  mark_def (int regno)
  {
    def8 |= 1 << regno;
    def16 |= 1 << regno;
    def32 |= 1 << regno;
  }

  inline void
  mark_hard (int regno)
  {
    hard |= 1 << regno;
  }

  /** clear usage of full register. */
  inline void
  unset (int regno)
  {
    use8 &= ~(1 << regno);
    use16 &= ~(1 << regno);
    use32 &= ~(1 << regno);
    def8 &= ~(1 << regno);
    def16 &= ~(1 << regno);
    def32 &= ~(1 << regno);
    hard &= ~(1 << regno);
  }

  /** a register is used if at least a byte is read. */
  inline unsigned
  get_use () const
  {
    return use8 | use16 | use32;
  }

  inline void
  copy_use (const insn_info & u)
  {
    use8 = u.use8;
    use16 = u.use16;
    use32 = u.use32;
  }

  /** a register is used if at least a byte is read. */
  inline unsigned
  get_myuse () const
  {
    return myuse8 | myuse16 | myuse32;
  }

  /** a register is defined if at least a byte is set. */
  inline unsigned
  get_def () const
  {
    return def8;
  }

  inline unsigned
  get_hard () const
  {
    return hard;
  }

  inline bool
  is_use (int regno) const
  {
    return ((use8 | use16 | use32) & (1 << regno)) != 0;
  }

  inline unsigned
  is_use_hi24 (int regno) const
  {
    return ((use16 | use32) & (1 << regno)) != 0;
  }

  inline unsigned
  is_use32 (int regno) const
  {
    return ((use32) & (1 << regno)) != 0;
  }

  inline int
  getX(int regno) const
  {
    return ((use8 & (1 << regno)) ? 1 : 0) + ((use16 & (1 << regno)) ? 2 : 0) + ((use32 & (1 << regno)) ? 4 : 0);
  }

  inline bool
  is_myuse (int regno)
  {
    return ((myuse8 | myuse16 | myuse32) & (1 << regno)) != 0;
  }

  inline bool
  is_def (int regno)
  {
    return (def8 & (1 << regno)) != 0;
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
    def8 = 0;
    def16 = 0;
    def32 = 0;
  }

  inline void
  rename_def (unsigned oldbit, unsigned newbit)
  {
    if (def8 & oldbit)
      {
	def8 |= newbit;
	def8 &= ~oldbit;
      }
    if (def16 & oldbit)
	{
	  def16 |= newbit;
	  def16 &= ~oldbit;
	}
    if (def32 & oldbit)
	{
	  def32 |= newbit;
	  def32 &= ~oldbit;
	}
  }
  inline void
  rename (unsigned oldbit, unsigned newbit)
  {
    rename_def(oldbit, newbit);
    if (use8 & oldbit)
      {
	use8 |= newbit;
	use8 &= ~oldbit;
      }
    if (use16 & oldbit)
      {
	use16 |= newbit;
	use16 &= ~oldbit;
      }
    if (use32 & oldbit)
      {
	use32 |= newbit;
	use32 &= ~oldbit;
      }
    if (myuse8 & oldbit)
      {
	myuse8 |= newbit;
	myuse8 &= ~oldbit;
      }
    if (myuse16 & oldbit)
      {
	myuse16 |= newbit;
	myuse16 &= ~oldbit;
      }
    if (myuse32 & oldbit)
      {
	myuse32 |= newbit;
	myuse32 &= ~oldbit;
      }
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
    use8 &= ~o.def8;
    use8 |= o.use8;
    def8 = 0;
    use16 &= ~o.def16;
    use16 |= o.use16;
    def16 = 0;
    use32 &= ~o.def32;
    use32 |= o.use32;
    def32 = 0;
  }

  inline insn_info &
  merge (insn_info const & o)
  {
    myuse8  = o.myuse8;
    myuse16 = o.myuse16;
    myuse32 = o.myuse32;
    use8  = (use8 & ~o.def8) | o.use8;
    use16 = (use16 & ~o.def16) | o.use16;
    use32 = (use32 & ~o.def32) | o.use32;
    def8  |= o.def8;
    def16 |= o.def16;
    def32 |= o.def32;

    hard |= o.hard;
    multi_reg = o.multi_reg;
    return *this;
  }

  inline insn_info &
  or_def (insn_info const & o)
  {
    def8  |= o.def8;
    def16 |= o.def16;
    def32 |= o.def32;
    return *this;
  }

  inline insn_info &
  make_hard ()
  {
    hard |= use8 | def8;
    return *this;
  }

  inline insn_info &
  make_clobber (machine_mode mode )
  {
    hard = use8 = def8 = use8 | def8;
    if (GET_MODE_SIZE(mode) > 1)
      {
	use16 = def16 = use16 | def16;
	if (GET_MODE_SIZE(mode) > 2)
	  use32 = def32 = use32 | def32;
      }
    return *this;
  }

  inline bool
  contains (insn_info const & o) const
  {
    if ((o.def8) & ~(def8))
      return false;
    if ((o.def16) & ~(def16))
      return false;
    if ((o.def32) & ~(def32))
      return false;
    if ((o.use8) & ~(use8))
      return false;
    if ((o.use16) & ~(use16))
      return false;
    if ((o.use32) & ~(use32))
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
  make_post_inc (int regno, int addend);

  void
  auto_inc_fixup (int regno, int size, int addend);

  void
  patch_mem_offsets(rtx x, int size);

  /* return bits for alternate free registers. */
  unsigned
  get_free_mask () const
  {
    if (def8 & hard)
      return 0;

    if (!def8)
      return 0;

    unsigned def_no_cc = def8 & ~(1 << FIRST_PSEUDO_REGISTER);
    if (def_no_cc > 0x4000)
      return 0;

    unsigned mask = def_no_cc - 1;
    /* more than one register -> don't touch. */
    if ((mask & ~def8) != mask)
      return 0;

    if (def_no_cc > 0xff)
      mask &= 0xff00;

    return mask & ~(use8|use16|use32);
  }

  unsigned
  get_regbit () const
  {
    if (GET_MODE_SIZE(mode) > 4)
      return 0;
    return (def8|def16|def32) & ~hard & ~(use8|use16|use32) & 0x7fff;
  }

  void
  set_insn (rtx_insn * newinsn);

  void
  a5_to_a7 (rtx a7, int add);
};

bool
insn_info::make_post_inc (int regno, int addend)
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
  rtx mem;

  if (get_dst_mem_regno () == regno)
    mem = SET_DEST(set);
  else
    {
      mem = SET_SRC(set);
      if (!MEM_P(mem))
	{
	  const char * format = GET_RTX_FORMAT(GET_CODE(mem));
	  if (format[0] != 'e')
	    return 0;
	  if (format[1] == 'e')
	    mem = XEXP(mem, 1);
	  else
	    mem = XEXP(mem, 0);
	}
    }

  if (!MEM_P(mem))
    return 0;

  rtx reg = XEXP(mem, 0);
  if (addend < 0)
    {
      if (GET_CODE(reg) != PLUS)
	return 0;
      reg = XEXP(reg, 0);
    }

  if (!REG_P(reg))
    return 0;

  XEXP(mem, 0) = gen_rtx_POST_INC(SImode, reg);

  if (insn_invalid_p (new_insn, 0))
    {
      XEXP(mem, 0) = reg;
      insn_invalid_p (insn, 0);
      return 0;
    }

  SET_INSN_DELETED(insn);
  (get_dst_mem_regno () == regno ? dst_autoinc : src_autoinc) = GET_MODE_SIZE(mode);
  insn = emit_insn_after (PATTERN (new_insn), insn);
  add_reg_note (insn, REG_INC, reg);
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

void insn_info::patch_mem_offsets(rtx x, int offset)
{
  if (MEM_P(x))
    {
      rtx plus = XEXP(x, 0);

      if (offset == 0)
	XEXP(x, 0) = XEXP(plus, 0);
      else
	XEXP(plus, 1) = gen_rtx_CONST_INT (VOIDmode, offset);

      return;
    }

  const char * format = GET_RTX_FORMAT(GET_CODE(x));
  if (format[0] == 'e')
    patch_mem_offsets(XEXP(x, 0), offset);
  if (format[1] == 'e')
    patch_mem_offsets(XEXP(x, 1), offset);
}

void
insn_info::auto_inc_fixup (int regno, int size, int addend)
{
  // fprintf(stderr, ":::"); debug_rtx (insn);
  rtx set0 = single_set (insn);
  rtx set = set0;
  if (is_compare ())
    set = SET_SRC(set);

  // add to register
  if (get_src_op () == PLUS && !is_src_mem() && !is_dst_mem())
    {
      rtx src = SET_SRC(set);
      if (get_src_intval () == size)
	{
	  src_intval = 0;
	  src_plus = false;
	  src_op = (rtx_code)0;
	  SET_SRC(set) = XEXP(src, 0);
	  SET_INSN_DELETED(insn);
	  return;
	}

	XEXP(src, 1) = gen_rtx_CONST_INT (VOIDmode, src_intval -= size);
    }
  else if (get_src_mem_regno () == regno)
    {
      int offset = get_src_mem_addr() - size * addend;
      patch_mem_offsets(SET_SRC(set), offset);
      if (offset == 0)
	src_mem_addr = 0;
      else
	src_mem_addr = offset;
    }
  if (get_dst_mem_regno () == regno)
    {
      int offset = get_dst_mem_addr() - size * addend;
      patch_mem_offsets(SET_DEST(set), offset);
      dst_mem_addr = offset;
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
	  mark_myuse (0, sz/8);
	  if (sz > 32)
	    {
	      mark_hard (1);
	      mark_myuse (1, 4);
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
	    {
	      if (REG_NREGS(reg) > 1)
		for (unsigned r = REGNO(reg); r < END_REGNO (reg); ++r)
		  mark_myuse (r, 4);
	      else
		mark_myuse (reg);
	    }
	}
      /* mark stack pointer used. there could be parameters on stack*/
      mark_myuse (15, 4);
      /* mark scratch registers. */
      mark_def (0);
      mark_def (1);
      mark_def (8);
      mark_def (9);
      mark_def (16);
      mark_def (17);
      /* also mark all registers as not renamable */
      hard = use8;
    }
  if (CALL_P(insn) || ANY_RETURN_P(pattern))
    {
      for (unsigned i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
	if (global_regs[i])
	  {
	    mark_hard (i);
	    mark_myuse(i, 4);
	  }
    }
  scan_rtx (pattern);
}

/* scan rtx for registers and set the corresponding flags. */
void
insn_info::scan_rtx (rtx x)
{
  if (REG_P(x) || ((GET_CODE(x) == STRICT_LOW_PART || GET_CODE(x) == SUBREG) && REG_P(XEXP(x, 0))))
    {
      if (!REG_P(x))
        x = XEXP(x, 0);
        
      int n0 = REG_NREGS(x);
      if (n0 > 1)
	{
	  for (int n = n0, r = REGNO(x); n > 0; --n, ++r)
	    {
	      mark_myuse (r, 4);
	      multi_reg |= 1<<r;
	    }
	}
      else
	mark_myuse(x);
      return;
    }

  if (x == cc0_rtx)
    {
      mark_myuse (FIRST_PSEUDO_REGISTER, 4);
      return;
    }

  RTX_CODE code = GET_CODE(x);

  /* handle SET and record use and def. */
  if (code == SET)
    {
      unsigned u8 = use8;
      unsigned u16 = use16;
      unsigned u32 = use32;
      unsigned mu8 = myuse8;
      unsigned mu16 = myuse16;
      unsigned mu32 = myuse32;
      use8  = myuse8 = 0;
      use16 = myuse16 = 0;
      use32 = myuse32 = 0;
      rtx dst = SET_DEST(x);
      scan_rtx (dst);
      if (REG_P(dst) || ((GET_CODE(dst) == STRICT_LOW_PART || GET_CODE(dst) == SUBREG) && REG_P(XEXP(dst, 0))))
	{
	  def8 |= use8;
	  def16 |= use16;
	  def32 |= use32;

	  use8 = u8;
	  myuse8 = mu8;
	  use16 = u16;
	  myuse16 = mu16;
	  use32 = u32;
	  myuse32 = mu32;
	}

      // avoid side effects from myuse -> def, e.g. adding the dst reg to def by src auto inc
      mu8 = myuse8;
      mu16 = myuse16;
      mu32 = myuse32;

      myuse8 = 0;
      myuse16 = 0;
      myuse32 = 0;
      // this updates myuse8/16/32
      scan_rtx (SET_SRC(x));
      myuse8  |= mu8;
      myuse16 |= mu16;
      myuse32 |= mu32;

      int code = GET_CODE(SET_SRC(x));
      if (code == ASM_OPERANDS)
	hard |= def8 | use8 | use16 | use32;
      return;
    }

  if (code == TRAP_IF)
    {
      /* mark all registers used. */
      hard = use8 = myuse8 = use16 = myuse16 = use32 = myuse32 = (1 << FIRST_PSEUDO_REGISTER) - 1;
      return;
    }

  unsigned prevu16 = use16;
  unsigned prevu32 = use32;

  const char *fmt = GET_RTX_FORMAT(code);
  for (int i = GET_RTX_LENGTH (code) - 1; i >= 0; i--)
    {
      if (fmt[i] == 'e')
	scan_rtx (XEXP(x, i));
      else if (fmt[i] == 'E')
	for (int j = XVECLEN (x, i) - 1; j >= 0; j--)
	  {
	    unsigned u8  = use8;
	    unsigned u16 = use16;
	    unsigned u32 = use32;
	    unsigned mu8  = myuse8;
	    unsigned mu16 = myuse16;
	    unsigned mu32 = myuse32;
	    unsigned d8  = def8;
	    unsigned d16 = def16;
	    unsigned d32 = def32;
	    unsigned mr = multi_reg;
	    scan_rtx (XVECEXP(x, i, j));
	    use8  |= u8;
	    use16 |= u16;
	    use32 |= u32;
	    myuse8  |= mu8;
	    myuse16 |= mu16;
	    myuse32 |= mu32;
	    def8  |= d8;
	    def16 |= d16;
	    def32 |= d32;
	    multi_reg |= mr;
	    if ((def8 - 1) & def8)
	      multi_reg |= def8;
	  }
    }

  /* handle
   * AND.W (REG 255)
   * AND.L (REG 255)
   * AND.L (REG 65535)
   * to reduce the use
   */
  if (code == AND && REG_P (XEXP (x, 0)) && CONST_INT_P (XEXP (x, 1)))
    {
      unsigned regno = REGNO (XEXP (x, 0));
      unsigned val = INTVAL (XEXP (x, 1));
      if (val <= 0xff)
	{
	  myuse32 &= ~(1<<regno);
	  use32 = prevu32 | myuse32;
	  myuse16 &= ~(1<<regno);
	  use16 = prevu16 | myuse16;
	}
      else if (val <= 0xffff)
	{
	  myuse32 &= ~(1<<regno);
	  use32 = prevu32 | myuse32;
	}
    }


  if (code == POST_INC || code == PRE_DEC || code == CLOBBER)
    {  def8 |= myuse8; def16 |= myuse16; def32 |= myuse32;}
  if (code == CLOBBER)
    multi_reg |= def8;
}

void
insn_info::fledder_src_mem (rtx src)
{
  memset(&src_addr, 0, sizeof(dst_addr));
  src_mem = true;
  decompose_mem (GET_MODE_SIZE(mode), &XEXP(src, 0), &src_addr, 1);
  src_autoinc = src_addr.code != 0 && src_addr.code != MEM;

  if (src_addr.offset && ! SYMBOL_REF_P(src_addr.offset) && GET_CODE(src_addr.offset) != LABEL_REF && GET_CODE(src_addr.offset) != UNSPEC)
    {
      if (CONST_INT_P(src_addr.offset))
	{
	  src_mem_addr = INTVAL(src_addr.offset);
	  src_addr.offset = 0;
	}
      else // PLUS
	{
	  src_mem_addr = INTVAL(XEXP(src_addr.offset, 1));
	  src_addr.offset = XEXP(src_addr.offset, 0);
	}
    }
}

void
insn_info::fledder_dst_mem (rtx dst)
{
  memset(&dst_addr, 0, sizeof(dst_addr));
  dst_mem = true;
  decompose_mem (GET_MODE_SIZE(mode), &XEXP(dst, 0), &dst_addr, 1);
  dst_autoinc = dst_addr.code != 0 && dst_addr.code != MEM;

  if (dst_addr.offset && ! SYMBOL_REF_P(dst_addr.offset) && GET_CODE(dst_addr.offset) != LABEL_REF && GET_CODE(dst_addr.offset) != UNSPEC)
    {
      if (CONST_INT_P(dst_addr.offset))
	{
	  dst_mem_addr = INTVAL(dst_addr.offset);
	  dst_addr.offset = 0;
	}
      else // PLUS
	{
	  dst_mem_addr = INTVAL(XEXP(dst_addr.offset, 1));
	  dst_addr.offset = XEXP(dst_addr.offset, 0);
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

  if (GET_CODE(src) == FIX)
    src = XEXP(src, 0);

  mode = GET_MODE(dst);
  if (mode == VOIDmode)
    mode = GET_MODE(src);

  if (REG_P(dst))
    {
      dst_reg = dst;
    }
  else if (MEM_P(dst))
    {
      fledder_dst_mem(dst);
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
find_regs_by_no (rtx x, unsigned oldregno,std::set<rtx *> & regs)
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
		regs.insert(&XEXP(x, i));
	    }
	  else
	    find_regs_by_no (y, oldregno, regs);
	}
      else if (fmt[i] == 'E')
	for (int j = XVECLEN (x, i) - 1; j >= 0; j--)
	  {
	    rtx z = XVECEXP(x, i, j);
	    find_regs_by_no (z, oldregno, regs);
	  }
    }
}

/*
 * Collect some data.
 */
static std::vector<insn_info> *infos;
typedef std::vector<insn_info>::iterator insn_info_iterator;

// insn->u2.insn_uid -> rtx_insn *
static std::multimap<int, rtx_insn *> *label2jump;
typedef std::multimap<int, rtx_insn *>::iterator l2j_iterator;

// index -> index
static std::multimap<unsigned, unsigned> *jump2label;
typedef std::multimap<unsigned, unsigned>::iterator j2l_iterator;

static std::map<rtx_insn *, insn_info *> *insn2info;
typedef std::map<rtx_insn *, insn_info *>::iterator i2i_iterator;

static std::set<unsigned> *scan_starts;
typedef std::set<unsigned>::iterator su_iterator;

static insn_info * info0;
static unsigned usable_regs;

static void
update_insn_infos (std::set<unsigned> & todo = *scan_starts);
static unsigned
track_regs ();

static void
update_insn2index ()
{
  infos->reserve (infos->size () * 8 / 7 + 2);
  insn2info->clear ();
  /* needs a separate pass since the insn_infos require fixed addresses for ->get_index() */
  for (unsigned i = 0; i < infos->size (); ++i)
    {
      insn_info & ii = (*infos)[i];
      insn2info->insert (std::make_pair (ii.get_insn (), &ii));
    }
  info0 = &(*infos)[0];
}

static void
update_label2jump ()
{
  update_insn2index ();
  jump2label->clear();

  for (unsigned index = 0; index < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];
      if (ii.is_label ())
	for (l2j_iterator i = label2jump->find (ii.get_insn ()->u2.insn_uid), k = i;
	    i != label2jump->end () && i->first == k->first; ++i)
	  jump2label->insert (std::make_pair (insn2info->find (i->second)->second->get_index (), index));
    }
}

int
insn_info::get_index () const
{
  insn_info * ii = &(*infos)[0];

  if (ii == info0)
    {
      ptrdiff_t diff = ((char const *) this - (char const *) ii);
      unsigned pos = diff / sizeof(insn_info);
      if (pos < infos->size ())
	return pos;
    }

// realloc happened...
  for (unsigned i = 0; i < infos->size (); ++i)
    if ((*infos)[i].get_insn () == this->insn)
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
  insn2info->insert (std::make_pair (insn, this));
// usage flags did not change
}

void
insn_info::swap_adds (rtx_insn * newinsn, insn_info & ii)
{
  insn = newinsn;

  std::swap (*this, ii);

  insn2info->insert (std::make_pair (insn, this));
  insn2info->insert (std::make_pair (ii.insn, &ii));

// usage flags did not change
}

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
  if (proepi == IN_EPILOGUE && get_src_mem_regno () == FRAME_POINTER_REGNUM)
    {
      rtx set = single_set (insn);
      if (set)
	{
	  SET_SRC(set) = gen_rtx_MEM (mode, gen_rtx_POST_INC(SImode, a7));
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
  rtx reg = gen_raw_REG (SImode, regno);
  bool vola = src->volatil;

  if (is_dst_mem () && (has_dst_addr () || get_dst_symbol ()) && !has_dst_memreg () && get_dst_mem_mem() == 0 && get_dst_symbol () == with_symbol)
    {
      unsigned addr = get_dst_mem_addr ();
      unsigned offset = addr - base;
      if (offset <= 0x7ffe)
	{
	  if (base == addr)
	    dst = gen_rtx_MEM (mode, reg);
	  else
	    dst = gen_rtx_MEM (mode, gen_rtx_PLUS(SImode, reg, gen_rtx_CONST_INT (SImode, offset)));

	  if (apply)
	    fledder_dst_mem (dst);
	}
    }

  if (is_src_mem () && (has_src_addr () || get_src_symbol ()) && !has_src_memreg () && get_src_mem_mem() == 0 && get_src_symbol () == with_symbol)
    {
      unsigned addr = get_src_mem_addr ();
      unsigned offset = addr - base;
      if (offset <= 0x7ffe)
	{
	  if (base == addr)
	    src = gen_rtx_MEM (mode, reg);
	  else
	    src = gen_rtx_MEM (mode, gen_rtx_PLUS(SImode, reg, gen_rtx_CONST_INT (SImode, offset)));

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
	    fledder_src_mem(src);
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

  mark_myuse (regno, 4);

  insn2info->insert (std::make_pair (insn, this));
}
/*
 * Reset collected data.
 */
static void
clear (void)
{
  label2jump->clear ();
  jump2label->clear ();
  insn2info->clear ();
  infos->clear ();
  scan_starts->clear ();
}

/*
 *  return true if the register is DEAD.
 *  Do not check at jumps.
 */
static bool
is_reg_dead (unsigned regno, unsigned _pos)
{
// skip labels.
  for (unsigned pos = _pos + 1; pos < infos->size (); ++pos)
    {
      insn_info & ii = (*infos)[pos];
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
  i2i_iterator i = insn2info->find (insn);
  if (i == insn2info->end ())
    return;

  insn_info & jj = *i->second;
  unsigned index = jj.get_index ();
  if (index + 1 < infos->size ())
    ++index;
  insn_info & ii = (*infos)[index];

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
  i2i_iterator i = insn2info->find (insn);
  if (i == insn2info->end ())
    return;

  insn_info & ii = *i->second;

  if (f != stderr)
    {
      int cost = -1;
      rtx set = single_set(ii.get_insn());
      if (set)
	cost = rtx_cost(set, GET_MODE(SET_DEST(set)), INSN, 0, true);
      else if (ii.is_call())
	cost = rtx_cost(PATTERN(ii.get_insn()), VOIDmode, INSN, 0, true);
      if (be_very_verbose)
	fprintf (f, "\n\t\t\t\t#%d\t%d %d\t", ii.get_index (), cost, set ? insn_rtx_cost(set, true): 0);
      else
	{
	  fprintf (f, "\t# %d %d", cost, set ? insn_rtx_cost(set, true): 0);
	  return;
	}
    }

  fprintf (f, "%c ", ii.in_proepi () == IN_PROLOGUE ? 'p' : ii.in_proepi () >= IN_EPILOGUE ? 'e' : ' ');

  for (int j = 0; j < 8; ++j)
    if (ii.is_use (j) || ii.is_def (j))
      {
	fprintf (f, ii.is_hard (j) ? "!" : " ");
	fprintf (f, ii.is_def (j) ? ii.is_use (j) ? "*" : "+" : ii.is_myuse (j) ? "." : " ");
	fprintf (f, "%d", ii.getX(j));
	fprintf (f, "d%d", j);
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

  if (ii.is_use (FIRST_PSEUDO_REGISTER) || ii.is_def (FIRST_PSEUDO_REGISTER))
    {
      fprintf (f, ii.is_def (FIRST_PSEUDO_REGISTER) ? ii.is_use (FIRST_PSEUDO_REGISTER) ? "*" : "+" : ii.is_myuse (FIRST_PSEUDO_REGISTER) ? "." : " ");
      fprintf (f, "cc ");
    }
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
      for (rtx_insn * insn = get_insns (); insn && insn != (*infos)[0].get_insn (); insn = NEXT_INSN (insn))
	debug_rtx (insn);
    }
  for (unsigned i = 0; i < infos->size (); ++i)
    {
      fprintf (stderr, "%d: ", i);

      rtx_insn * insn = (*infos)[i].get_insn ();
      if (i < infos->size ())
	append_reg_usage (stderr, insn);

      fprintf (stderr, "\t");
      debug_rtx (insn);

      if (all)
	{
	  rtx_insn * p = i + 1 < infos->size () ? (*infos)[i + 1].get_insn () : 0;
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
 *
 * todo defaults to scan_starts
 */
static void
update_insn_infos (std::set<unsigned> & todo)
{
  /* add all return (jump outs) and start analysis there. */
  if (todo.begin () == todo.end ())
    todo.insert (infos->size () - 1);

  bool locka4 = flag_pic >= 3;

  while (!todo.empty ())
    {
      int start = *todo.begin ();
      todo.erase (todo.begin ());
      insn_info ii = (*infos)[start];

      enum proepis proepi = ii.in_proepi ();

      // mark sp reg as used.
      if (proepi >= IN_EPILOGUE)
	{
	  ii.mark_use (STACK_POINTER_REGNUM);
	  (*infos)[start].mark_use (STACK_POINTER_REGNUM);
	}

      for (int pos = start; pos >= 0; --pos)
	{
	  insn_info & pp = (*infos)[pos];
	  rtx_insn * insn = pp.get_insn ();

	  if (!insn || NOTE_P (insn))
	    continue;

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
	      l2j_iterator i = label2jump->find (insn->u2.insn_uid);

	      /* no jump to here -> mark all registers as hard regs.
	       * This label is maybe used in an exception handler.
	       * Marking as hard also avoids stack frame removal.
	       */
	      if (i == label2jump->end ())
		(*infos)[pos + 1].make_hard ();
	      else
		for (l2j_iterator k = i; i != label2jump->end () && i->first == k->first; ++i)
		  {
		    i2i_iterator j = insn2info->find (i->second);
		    if (j != insn2info->end ())
		      {
			unsigned index = j->second->get_index ();
			insn_info & jj = (*infos)[index];
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
	      if (pos > 0 && (*infos)[pos - 1].is_jump ())
		{
		  rtx_insn * prev = (*infos)[pos - 1].get_insn ();
		  rtx set = single_set (prev);
		  /* unconditional? -> break! */
		  if ( (set && SET_DEST (set) == pc_rtx && GET_CODE(SET_SRC(set)) != IF_THEN_ELSE)
		    || (!set && PATTERN(prev) && GET_CODE(PATTERN(prev)) == PARALLEL &&  GET_CODE (SET_SRC (XVECEXP (PATTERN(prev), 0, 0))) != IF_THEN_ELSE))
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
		  su_iterator k = scan_starts->find (pos);
		  if (k != scan_starts->end ())
		    {
		      pp.clear_visited ();
		      break;
		    }
		}
	    }
	  else if (GET_CODE (pattern) == USE || GET_CODE (pattern) == CLOBBER)
	    {
	      use.make_clobber (GET_MODE(XEXP(pattern, 0)));
	    }
	  else if (single_set (insn) == 0)
	    use.make_hard ();
	  else
	  /* if not cc0 defined check for mod. */
	  if (!use.is_def (FIRST_PSEUDO_REGISTER))
	    {
	      CC_STATUS_INIT;
	      NOTICE_UPDATE_CC(PATTERN (insn), insn);
	      if (cc_status.value1 || cc_status.value2)
		use.mark_def (FIRST_PSEUDO_REGISTER);
	    }

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
  for (unsigned i = 0; i < infos->size (); ++i)
    {
      insn_info & ii = (*infos)[i];
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

	  infos->push_back (insn_info (insn, inproepilogue));
	  insn_info & ii = (*infos)[infos->size () - 1];

	  if (JUMP_P(insn))
	    {
	      if (inproepilogue || ANY_RETURN_P(PATTERN (insn)))
		{
		  if (ANY_RETURN_P(PATTERN (insn)))
		    ii.set_proepi (IN_EPILOGUE);

		  scan_starts->insert (infos->size () - 1);
		  inproepilogue = IN_CODE;
		  rtx set = single_set (insn);
		  if (ANY_RETURN_P(PATTERN (insn))
		      || (set && SET_DEST(set) == pc_rtx && GET_CODE(SET_SRC(set)) != IF_THEN_ELSE)
 	              || (!set && PATTERN(insn) && GET_CODE(PATTERN(insn)) == PARALLEL && GET_CODE (SET_SRC (XVECEXP (PATTERN(insn), 0, 0))) != IF_THEN_ELSE))
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
			      label2jump->insert (std::make_pair (label->u2.insn_uid, insn));
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
		  label2jump->insert (std::make_pair (label->u2.insn_uid, insn));
		}
	    }
	  else if (LABEL_P(insn))
	    {
	      ii.mark_label ();
	      ii.set_proepi (inproepilogue = IN_CODE);
	      if (infos->size () > 1)
		scan_starts->insert (infos->size () - 1);
	    }
	  else if (CALL_P(insn))
	    {
	      if (insn->jump)
		{
		  ii.set_proepi (IN_EPILOGUE);
		  ii.mark_jump ();
		  scan_starts->insert (infos->size () - 1);
		}
	      ii.mark_call ();
	      if (inproepilogue)
		{
		  scan_starts->insert (infos->size () - 1);
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
  scan_starts->insert (infos->size () - 1);
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
      insn_info & ii = (*infos)[index];
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

      insn_info & jj = (*infos)[start];

      /* stop at labels. If a label is a start pos, a search is maybe started again. */
      if (jj.is_label ())
	break;

      /* do not run over RETURNS */
      insn_info & bb = (*infos)[startm1];
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
static void
rus(char const * title)
{
  fputs(title, stderr);
  fputs("\n", stderr);
  for (unsigned index = 0; index < infos->size (); ++index)
    {
      fprintf(stderr, "%d\t", index);
      append_reg_usage(stderr, (*infos)[index].get_insn());
    }
}
*/

/*
 * Always prefer lower register numbers within the class.
 */
static unsigned
opt_reg_rename (void)
{
  update_label2jump ();

  if (infos->size () < 2)
    return 0;

  unsigned changes = 0;

//  rus("opt_reg_rename");

//  dump_insns ("rename", 1);
  for (unsigned index = 0; index < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];

      /* do not rename if register is hard or used in same statement. */
      const unsigned rename_regbit = ii.get_regbit ();
      if (!rename_regbit)
	continue;

      const unsigned rename_regno = bit2regno (rename_regbit);

      /* part of multi registers? do not touch! */
      if (ii.get_multi_reg () & rename_regbit)
	continue;

      /* get the mask for free registers. */
      unsigned mask = ii.get_free_mask () & (rename_regbit - 1);

      /* no rename from ax to dy. */
      if (rename_regno > 7)
	mask &= 0xff00;

      /* If it's a full register assignment, add the source register.
       * Add this register anyway and track it's modification too.
       * But only during first pass to avoid endless renames. */
      unsigned reusemask = 0;
      if (pass == 1 && ii.is_src_reg() && ii.get_mode() == SImode)
        mask |= reusemask = 1 << ii.get_src_regno ();

      mask &= usable_regs;

      /* do not use a4 if compiling baserel */
      if (flag_pic >= 3)
	mask &= ~(1 << PIC_REG);

      if (!mask)
	continue;

      /* first = pos to start, second indicates to treat def as use. */
      std::set<unsigned> todo;
      std::set<unsigned> found;
      std::set<unsigned> endings;
      if (index + 1 < infos->size ())
	todo.insert (index + 1);

      found.insert (index);
      /* a register was defined, follow all branches. */
      while (mask && todo.begin () != todo.end ())
	{
	  unsigned runpos = *todo.begin ();
	  todo.erase (todo.begin ());

//	  printf ("runpos %d \n", runpos); fflush (stdout);
	  for (unsigned pos = runpos; mask && pos < infos->size (); ++pos)
	    {
	      /* already searched. */
	      if (found.find (pos) != found.end ())
		break;

	      insn_info & jj = (*infos)[pos];
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
		  for (l2j_iterator i = label2jump->find (insn->u2.insn_uid), k = i;
		      i != label2jump->end () && i->first == k->first; ++i)
		    {
		      i2i_iterator j = insn2info->find (i->second);
		      if (j == insn2info->end ())
			{
			  mask = 0;
			  break;
			}

		      unsigned startat = j->second->get_index ();
		      if (found.find (startat) == found.end () && (*infos)[startat].is_use (rename_regno))
			{
			  unsigned start = find_start (startat, rename_regno);
    //		      printf ("label %d <- jump %d : start %d\n", pos, startat, start); fflush (stdout);
			  todo.insert (start);
			}
		    }

		  /* if this label is at a start, check if it is reachable from the previous insn,
		   * and if, check for use then search start. */
		  if (pos > 0)
		    {
		      insn_info & bb = (*infos)[pos - 1];
//		      rtx set = single_set (bb.get_insn ());
		      if (ANY_RETURN_P(bb.get_insn ())
//			  || (set && SET_DEST(set) == pc_rtx && GET_CODE(SET_SRC(set)) != IF_THEN_ELSE)
//			  || (!set && PATTERN(bb.get_insn()) && GET_CODE(PATTERN(bb.get_insn())) == PARALLEL && (GET_CODE (SET_SRC (XVECEXP (PATTERN(bb.get_insn()), 0, 0)))) != IF_THEN_ELSE)
			  )

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

	      // if a register is reused in a tail rename
	      // check for modifications
	      if (reusemask)
		{
		  if (jj.get_def() & reusemask)
		    {
		      // the reused is modified - tail rename not possible
		      mask &= ~reusemask;
		      reusemask = 0;
		    }
		  else if ((jj.get_def() & rename_regbit) && (jj.get_use() & reusemask))
		    {
		      // if the register is modified, the reused reg must be dead
		      mask &= ~reusemask;
		      reusemask = 0;
		    }
		}

	      /* not used. and not a def */
	      if (pos == runpos && (jj.get_def () & rename_regbit))
		{
		  /* continue since this pos was added by start search. */
		}
	      else if (!(jj.get_use () & rename_regbit))
		{
		  // search ends here and regrename is still valid.
		  endings.insert (pos);
		  break;
		}

	      /* abort if some insn using this reg uses more than 1 reg. */
	      if ((jj.get_myuse () & rename_regbit) && GET_MODE_SIZE(jj.get_mode()) > 4)
		{
		  mask = 0;
		  break;
		}

	      /* update free regs. */
	      mask &= ~jj.get_use ();
	      /* add the reused reg again. */
	      mask |= reusemask;
	      mask &= ~jj.get_def ();
	      mask &= ~jj.get_multi_reg();
	      if (!mask)
		break;

	      found.insert (pos);

	      /* follow jump and/or next insn. */
	      if (JUMP_P(insn))
		{
		  for (j2l_iterator i = jump2label->find (pos), k = i; i != jump2label->end () && i->first == k->first;
		      ++i)
		    {
		      unsigned label_index = i->second;

		      /* add the label to the search list. */
		      int labi = 0;

		      // search next non-label insn
		      insn_info * bb;
		      do
		        bb = &(*infos)[label_index + ++labi];
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
	  std::set<rtx *> regs;
//	  bool ok = true;
	  for (std::set<unsigned>::iterator i = found.begin (); i != found.end (); ++i)
	    {
	      insn_info & rr = (*infos)[*i];

//	      // prevent lea from or to data register.
//	      if (rr.get_src_op() == PLUS && rr.get_src_regno() != rr.get_dst_regno()) {
//		  if ((oldregno < 8 && newregno >= 8) || (oldregno >= 8 && newregno < 8)) {
//		      ok = false;
//		      break;
//		  }
//	      }

	      rtx_insn * insn = rr.get_insn ();

	      /* get rename modes. */
	      regs.clear();
	      find_regs_by_no(PATTERN (insn), oldregno, regs);
	      if (regs.size() > 0)
		{
		  for (std::set<rtx *>::iterator m = regs.begin(); m != regs.end(); ++m)
		    {
		      rtx *x = *m;
		      rtx to = gen_raw_REG (GET_MODE(*x), newregno);

		      validate_unshare_change(insn, x, to, true);
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
#if 1
	      unsigned oldbit = 1 << oldregno;
	      unsigned newbit = 1 << newregno;
	      // does not work yet: TODO: distinguish between, def, myuse and use!

//	      rus("quick update");

	      // update the analyzed info.
	      for (std::vector<unsigned>::iterator i = positions.begin (); i != positions.end (); ++i)
		{
		  rtx set = single_set((*infos)[*i].get_insn());
		  if (set)
		    (*infos)[*i].fledder(set);
		}


	      // update the insn_infos
	      found.erase(index);
	      (*infos)[index].rename_def(oldbit, newbit);

	      for (std::set<unsigned>::iterator i = found.begin (); i != found.end (); ++i)
		(*infos)[*i].rename(oldbit, newbit);

//	      rus("quick update");
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
  for (unsigned index = 1; index < infos->size (); ++index)
    {
      rtx_insn * insn = (*infos)[index].get_insn ();

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
		      rtx_insn * ii = (*infos)[*i].get_insn ();
		      rtx seti = single_set (ii);
		      rtx srci = SET_SRC(seti);
		      rtx dsti = SET_DEST(seti);
		      rtx_insn * jj = (*infos)[*j].get_insn ();
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
				  rtx_insn * check = (*infos)[k].get_insn ();
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
					    fixup -= GET_MODE_SIZE(GET_MODE(dst));
					  else if (GET_CODE(dst) == PRE_DEC ||
					  GET_CODE(dst) == POST_DEC)
					    fixup += GET_MODE_SIZE(GET_MODE(dst));
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
						fixup -= GET_MODE_SIZE(GET_MODE(dst));
					      else if (GET_CODE(dst) == PRE_DEC ||
					      GET_CODE(dst) == POST_DEC)
						fixup += GET_MODE_SIZE(GET_MODE(dst));
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
			      rtx_insn * before = (*infos)[current_label_index - 1].get_insn ();
			      rtx_insn * after = (*infos)[index + 1].get_insn ();
//			      rtx bset = single_set (before);

			      log ("(p) propagate_moves condition met, moving regs %s, %s\n",
			      reg_names[REGNO(srci)],
				   reg_names[REGNO(dsti)]);

			      /* Move in front of loop and mark as dead. */
			      rtx_insn * newii = make_insn_raw (PATTERN (ii));
			      SET_INSN_DELETED(ii);

//			      /* Plus check if the reg was just loaded. */
//			      if (bset)
//				{
//				  rtx bdst = SET_DEST(bset);
//				  if (REG_P(bdst) && REGNO(bdst) == REGNO(srci))
//				    {
//				      SET_SRC(PATTERN(newii)) = SET_SRC(bset);
////					  SET_INSN_DELETED(ii);
//				    }
//				}
//			      else
				add_reg_note (newii, REG_DEAD, srci);

			      add_insn_after (newii, before, 0);

			      /* Move behind loop - into next BB. */
			      rtx_insn * newjj = make_insn_raw (PATTERN (jj));
			      add_insn_before (newjj, after, 0);
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
				      rtx_def * lbl = jump_out[k];
				      // search next no debug insn
				      rtx_def * before = next_nonnote_nondebug_insn (lbl);
				      //debug(before);
				      if ((REGNO(dsti) < 8 || REGNO(dstj) < 8) && REGNO(dsti) != REGNO(dstj))
					{
					  rtx move = gen_rtx_SET(dstj, dsti);
					  emit_insn_before (move, before);
					  if (fixups[k])
					    {
					      rtx neu = gen_rtx_SET(
						  dstj, gen_rtx_PLUS (Pmode, dstj, gen_rtx_CONST_INT (Pmode, fixups[k])));
					      emit_insn_before (neu, before);
					    }
					}
				      else if (fixups[k])
					{
					  rtx neu = gen_rtx_SET(
					      dstj, gen_rtx_PLUS (Pmode, dsti, gen_rtx_CONST_INT (Pmode, fixups[k])));
					  emit_insn_before (neu, before);
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
  rtx theReg = 0;
  unsigned int regno = FIRST_PSEUDO_REGISTER;

  for (unsigned index = 0; index < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];
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
	      if (REG_P(dst) && REGNO(dst) == REGNO(theReg) && CONST_INT_P(src) && INTVAL(src) == 0 && is_reg_dead (REGNO(dst), index))
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
	      theReg = SET_SRC(set);
	      continue;
	    }
	  x2reg = 0;
	}

      /* check for a match for x2reg. */
      if (x2reg == 0)
	{
	  if (ii.get_dst_reg() && ii.get_src_op() != ASM_OPERANDS)
	    {
	      x2reg = insn;
	      reg2x = 0;
	      regno = ii.get_dst_regno();
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

  for (unsigned index = 0; index + 1 < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];
      if (ii.get_dst_regno () < 8 || ii.get_dst_regno () > 15 || ii.get_src_op () != PLUS
	  || ii.get_src_regno () == ii.get_dst_regno () || !ii.get_src_intval ())
	continue;

      insn_info & jj = (*infos)[index + 1];

      if (!jj.get_dst_mem_reg () || jj.get_dst_mem_regno () != ii.get_src_regno () || jj.get_dst_mem_addr() || jj.get_dst_autoinc()
	  || jj.get_src_regno () == ii.get_dst_regno () || GET_MODE_SIZE(jj.get_mode()) != ii.get_src_intval () || jj.get_dst_mem_mem() != 0)
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
  if (infos->size () < 2)
    return change_count;

  unsigned lastsub = 0;
  for (unsigned index = infos->size () - 2; index > 0; --index)
    {
      insn_info & i1 = (*infos)[index];
      /* we wan't a compare or tst insn, */
      if (!i1.is_compare ())
	continue;

      if (GET_MODE_SIZE(i1.get_mode()) > 4 || !i1.is_dst_reg () || REGNO(i1.get_dst_reg()) > 7)
	continue;

      /* src must be a reg dead register with a constant - or a #0 */
      if (!i1.get_src_reg () && (!i1.is_src_const () || i1.get_src_op () == PLUS))
	continue;

      /* allow an alive reg, if life ends at previous handled sub. */
      int lastsubval = 0;
      if (lastsub == index + 3)
	{
	  insn_info & pp = (*infos)[lastsub];
	  if (pp.get_dst_regno () != i1.get_dst_regno ())
	    continue;
	  lastsubval = pp.get_src_intval ();

	  // but still check for usage after this jump
	  j2l_iterator l = jump2label->find (index + 2);
	  if (l == jump2label->end ())
	    continue;

	  insn_info & label = (*infos)[l->second + 1];
	  if (label.is_use (i1.get_dst_regno ()))
	    continue;
	}
      else if (!is_reg_dead (i1.get_dst_regno (), index))
	continue;

      insn_info & i0 = (*infos)[index - 1];
      int intval = 0;
      /* compare with register - check previous insn for load with constant. */
      if (i1.is_src_reg ())
	{
	  if (!is_reg_dead (i1.get_src_regno (), index))
	    continue;

	  if (GET_MODE_SIZE(i0.get_mode()) > 4)
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
      insn_info & i2 = (*infos)[index + 1];
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
	      insn_info & pp = (*infos)[lastsub];

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
  unsigned change_count = 0;
  for (unsigned index = 0; index + 2 < infos->size (); ++index)
    {
      insn_info & ii0 = (*infos)[index];
      insn_info & ii1 = (*infos)[index + 1];
      insn_info & ii2 = (*infos)[index + 2];

      if (!ii2.is_dst_reg () || ii2.is_src_mem() || ii2.get_src_op () != PLUS)
	{
	  index += 2;
	  continue;
	}

      if (!ii1.is_dst_reg () || ii1.is_src_mem() || ii1.get_src_op () != PLUS || ii1.get_dst_reg() != ii2.get_src_reg())
	{
	  ++index;
	  continue;
	}

      if (!ii0.is_dst_reg () || ii0.is_src_mem() || ii0.get_src_op () != PLUS)
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
//      debug_rtx(ii0.get_insn());
//      debug_rtx(ii1.get_insn());
//      debug_rtx(ii2.get_insn());

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
}

/* Update the insn_infos to 'know' the sp offset. */
static unsigned
track_sp (int & a5_touched)
{
// reset visited flags - also check if sp is used as REG src.
  for (unsigned index = 0; index < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];
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

      int sp_offset = (*infos)[startpos].get_sp_offset ();

      for (unsigned index = startpos; index < infos->size (); ++index)
	{
	  insn_info & ii = (*infos)[index];
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
		  for (l2j_iterator j = label2jump->find (ii.get_insn ()->u2.insn_uid), k = j;
		      j != label2jump->end () && j->first == k->first; ++j)
		    {
		      insn_info & ll = *insn2info->find(j->second)->second;
		      if (ll.is_visited () && ll.get_sp_offset () != sp_offset)
			return E_SP_MISMATCH;
		    }
		}

		// check the label(s) for this jump
		if (ii.is_jump ())
		  {
		    for (j2l_iterator i = jump2label->find (index), k = i; i != jump2label->end () && i->first == k->first; ++i)
		      {
			insn_info & ll = (*infos)[i->second];
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
		  for (l2j_iterator j = label2jump->find (ii.get_insn ()->u2.insn_uid), k = j;
		      j != label2jump->end () && j->first == k->first; ++j)
		{
		  insn_info & ll = *insn2info->find(j->second)->second;
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
	      for (j2l_iterator i = jump2label->find (index), k = i; i != jump2label->end () && i->first == k->first; ++i)
		{
		  insn_info & ll = (*infos)[i->second];
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
	    sp_offset += GET_MODE_SIZE(ii.get_mode()) * ii.get_dst_autoinc ();

	  // handle src mem autoinc
	  if (ii.is_src_mem () && ii.get_src_mem_regno () == STACK_POINTER_REGNUM && ii.get_src_autoinc ())
	    sp_offset += GET_MODE_SIZE(ii.get_mode()) * ii.get_src_autoinc ();
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
  if (!infos->size ())
    return 0;

  /* needed to track sp correctly. */
  update_label2jump ();
  int a5_touched = 0;
  if (track_sp (a5_touched))
    return 0; // do nothing on stack errors

  std::vector<int> a5pos;

  unsigned pos = 0;
  rtx_insn * insn = (*infos)[pos].get_insn ();
  if (JUMP_P(insn)) /* return -> empty function*/
    return 0;

  bool usea5 = false;
  int paramstart = 4;
  int a5offset = 0;

  /*
   * Move prologue to temp.
   * Only register push and parallel insn unless its a link a5 are moved.
   */
  unsigned num_push = 0;
  for (; pos < infos->size ();)
    {
      insn_info & ii = (*infos)[pos];
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
	  else
	    ++num_push;
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

      if (++pos >= infos->size ())
	{
	  return 0;
	}
    }

  if (pos == 0 || num_push >= 2)
    return 0;

  unsigned prologueend = pos;

  /* search epilogues - there can be multiple epilogues. */
  while (pos < infos->size ())
    {
      while (pos < infos->size ())
	{
	  if ((*infos)[pos].in_proepi () != IN_CODE)
	    break;
	  ++pos;
	}

      /* move epilogues away. */
      for (; pos < infos->size (); ++pos)
	{
	  insn_info & ii = (*infos)[pos];
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

  rtx a7 = gen_raw_REG (SImode, STACK_POINTER_REGNUM);
  rtx a5 = gen_raw_REG (SImode, FRAME_POINTER_REGNUM);

  unsigned changed = 0;
  unsigned adjust = 0;
  unsigned regs_seen = 0;
  unsigned regs_total_size = 0;
  /* now all push/pop insns are in temp. */
  for (unsigned i = 0; i < infos->size (); ++i)
    {
      insn_info & ii = (*infos)[i];
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
		    adjust += GET_MODE_SIZE(GET_MODE(reg));
		}
	      else
		{
		  regs_total_size += GET_MODE_SIZE(GET_MODE(reg));
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
			  rtx dec = gen_rtx_PRE_DEC(REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, a7);
			  rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, dec);
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
			      rtx plus = gen_rtx_PLUS(SImode, a5, gen_rtx_CONST_INT (SImode, a5offset + x));
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, plus);
			      rtx set = gen_rtx_SET(reg, mem);
			      emit_insn_before (set, insn);
			    }
			  else
			    {
			      /* pop */
			      rtx dec = gen_rtx_POST_INC(REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, a7);
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, dec);
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
		      plus = gen_rtx_PLUS(SImode, a7, gen_rtx_CONST_INT (SImode, i < prologueend ? -x : x));
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
			  plus = gen_rtx_PLUS(SImode, a7, gen_rtx_CONST_INT (SImode, -x));
			  x -= REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			  rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, plus);
			  rtx set = gen_rtx_SET(mem, regs[k]);
			  XVECEXP(parallel, 0, l) = set;
			}
		      else
			{
			  /* pop - use the same register as in the existing insn*/
			  if (ii.get_myuse () & (1 << FRAME_POINTER_REGNUM))
			    {
			      x += REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			      plus = gen_rtx_PLUS(SImode, a5, gen_rtx_CONST_INT (SImode, a5offset + x));
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, plus);
			      rtx set = gen_rtx_SET(regs[k], mem);
			      XVECEXP(parallel, 0, l) = set;
			    }
			  else
			    {
			      plus = x ? gen_rtx_PLUS(SImode, a7, gen_rtx_CONST_INT (SImode, x)) : a7;
			      x += REGNO(regs[k]) > STACK_POINTER_REGNUM ? 12 : 4;
			      rtx mem = gen_rtx_MEM (REGNO(regs[k]) > STACK_POINTER_REGNUM ? XFmode : SImode, plus);
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
		  regs_total_size += GET_MODE_SIZE(GET_MODE(src));
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
		      insn_info & pp = (*infos)[i - 1];
		      if (pp.is_stack() && (set = single_set(pp.get_insn())) && MEM_P(x = SET_SRC(set))
			  && GET_CODE(x = XEXP(x, 0)) == PLUS && REG_P(XEXP(x, 0)) && REGNO(XEXP(x, 0)) == FRAME_POINTER_REGNUM)
			{
			  XEXP(x, 1) = GEN_INT(INTVAL(XEXP(x, 1)) + GET_MODE_SIZE(GET_MODE(SET_SRC(set))));
			}
		    }

		}
	    }
	}
    }

  /* fix sp offsets. */
  if (!usea5 && adjust)
    {
      for (unsigned index = 0; index < infos->size (); ++index)
	{
	  insn_info & ii = (*infos)[index];
	  if (ii.in_proepi () != IN_CODE)
	    continue;

	  rtx pattern = PATTERN (ii.get_insn ());
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
	      SET_INSN_DELETED((*infos)[index].get_insn ());

	      // move to last insn in epilogue
	      while (index - 1 > 0 && (*infos)[index - 1].in_proepi () >= IN_EPILOGUE)
		--index;

	      insn_info & ii = (*infos)[index];
	      if (ii.in_proepi () >= IN_EPILOGUE && ii.get_sp_offset () != 0)
		{
		  log ("(f) adjusting exit sp\n");
		  rtx pattern = gen_rtx_SET(
		      a7, gen_rtx_PLUS (SImode, a7, gen_rtx_CONST_INT (SImode, ii.get_sp_offset ())));
		  emit_insn_before (pattern, ii.get_insn ());
		}
	    }

	  /* convert all parameter accesses via a5 into a7. */
	  for (unsigned i = 0; i < infos->size (); ++i)
	    {
	      insn_info & ii = (*infos)[i];

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
			      XEXP(plus, 1) = gen_rtx_CONST_INT (SImode, n);
			    }
			  else
			    {
			      XEXP(mem, 0) = XEXP(plus, 0);
			    }
			  n += GET_MODE_SIZE(GET_MODE(reg));
			  XVECEXP(parallel, 0, j + 1) = set;
			}

		      rtx a = copy_reg (a7, -1);
		      a->frame_related = 1;
		      rtx plus = gen_rtx_PLUS(SImode, a, gen_rtx_CONST_INT (SImode, regs_total_size));
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
 * Also the used bits per register are tracked.
 * This info is used to eliminate superfluous AND insns.
 */

static unsigned
track_regs ()
{
// reset visited flags
  for (unsigned index = 0; index < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];
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

      for (unsigned index = startpos; index < infos->size (); ++index)
	{
	  insn_info & ii = (*infos)[index];

	  // already visited?
	  if (index != startpos && ii.is_visited () && ii.get_track_var ()->no_merge_needed (track))
	    break;

	  // only keep common values at labels
	  if (ii.is_label ())
	    {
	      if (ii.is_visited ())
		{
		  ii.get_track_var ()->merge (track);
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
		{
		  // exception for autoinc
		  if (!ii.get_dst_reg() || !ii.get_src_autoinc())
		    track->clear_for_mask (def, index);
		  else
		    // mark only the auto inc register as unknown
		    track->clear(SImode, ii.get_src_mem_regno(), index);
		}
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

	      for (j2l_iterator i = jump2label->find (index), k = i; i != jump2label->end () && i->first == k->first; ++i)
		todo.insert (std::make_pair (i->second, new track_var (track)));

	      if (set && GET_CODE(SET_SRC(set)) == IF_THEN_ELSE)
		continue;

	      // dbra == parallel with IF_THEN_ELSE
	      if (!set && PATTERN(ii.get_insn()) && GET_CODE(PATTERN(ii.get_insn ())) == PARALLEL && GET_CODE(SET_SRC( XVECEXP (PATTERN(ii.get_insn ()), 0, 0) )) == IF_THEN_ELSE)
		continue;

	      // unconditional jump
	      break;
	    }

	  if (!set || !ii.get_def ())
	    continue;

	  if (dregno < 0)
	    {
	      rtx dst = SET_DEST(set);
	      track->invalidate_mem (dst, index);
	      if (ii.get_def())
		track->clear_for_mask(ii.get_def(), index);

	      // reverse assignment
	      if (MEM_P(dst) && (MEM_IN_STRUCT_P(dst) || MEM_READONLY_P(dst)) && ii.get_src_reg() && !ii.get_src_op())
  	        track->set (ii.get_mode (), ii.get_src_regno(), dst, ii.get_myuse(), index);

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
		      if (GET_MODE_SIZE(ii.get_mode()) == 2)
			dmask &= 0xffff;
		      else
		      if (GET_MODE_SIZE(ii.get_mode()) == 1)
			dmask &= 0xff;
		      if (ii.get_src_op() == LSHIFTRT)
			track->setMask(dregno, dmask >> INTVAL(op), ii.get_mode());
		      else if (ii.get_src_op() == ASHIFT)
			track->setMask(dregno, dmask << INTVAL(op), ii.get_mode());
		    }
		}
	      else
		track->clear (ii.get_mode (), dregno, index);
	      continue;
	    }

	  // WHY? or more than one register used: can't cache
//	  if (((ii.get_myuse () - 1) & ii.get_myuse ()))
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

static void
delete_and_update (unsigned index)
{
  SET_INSN_DELETED((*infos)[index].get_insn());
  int start = index + 1;
  while ((*infos)[start].is_label())
    ++start;
  scan_starts->insert(start);
  (*infos)[index + 1].clear_visited();
  update_insn_infos ();
}

/*
 * Some optimizations (e.g. propagate_moves) might result into an unused assignment behind the loop.
 * delete those insns.
 */
static unsigned
opt_elim_dead_assign (int blocked_regno)
{
  track_regs ();

//  unsigned mask = 0;

  unsigned change_count = 0;
  for (int index = infos->size () - 1; index >= 0; --index)
    {
      insn_info & ii = (*infos)[index];

      if (ii.is_compare ())
	{
	  if (blocked_regno == FIRST_PSEUDO_REGISTER && ii.get_dst_reg())
	    {
	      unsigned lmask = ii.get_track_var()->getMask(ii.get_dst_regno());
	      if (lmask != 0xffffffff)
		add_reg_note(ii.get_insn(), REG_BIT_MASK, gen_rtx_CONST_INT (SImode, lmask));
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

      rtx ssrc = SET_SRC(set);
      rtx_code opcode = GET_CODE(ssrc);

      // look for superfluous ZERO_EXTEND or SIGN_EXTEND
      if (opcode == ASHIFT || opcode == ASHIFTRT || opcode == LSHIFTRT)
	{
	  rtx op = XEXP(ssrc, 1);
	  if (REG_P (op))
	    {
	      int opreg = REGNO (op);
	      for (int jndex = index - 1; jndex > 0; --jndex)
		{
		  insn_info & jj = (*infos)[jndex];
		  if (jj.is_label())
		    break;

		  // ZERO_EXTEND and SIGN_EXTEND use and def that register.
		  if (jj.is_myuse(opreg))
		    {
		      if (jj.get_dst_regno() == opreg &&
			  (jj.get_src_op() == ZERO_EXTEND || jj.get_src_op() == SIGN_EXTEND))
			{
			  delete_and_update(jndex);
			  ++change_count;
			}
		      break;
		    }
		  // if the reg is set by something different break
		  if (jj.is_def(opreg))
		    break;
	        }
	    }
	  continue;
        }
      if (opcode == AND)
	{
	  track_var * tv = ii.get_track_var();
	  unsigned lmask = tv->getMask(ii.get_dst_regno());
	  rtx andval = XEXP(SET_SRC(set), 1);

	  if (REG_P(andval))
	    {
	      rtx val = tv->get(REGNO(andval));
	      if (val && GET_CODE(val) == CONST_INT)
		{
		  andval = 0;
		  long long int lli = INTVAL(val);
		  if (lli < 0x100000000LL)
		    andval = val;
		}
	    }
	  if (andval && GET_CODE(andval) == CONST_INT)
	    {
	      long long int lli = UINTVAL(andval);
	      if (lli < 0x100000000LL)
		{
		  unsigned nmask = lli;
		  if (GET_MODE_SIZE(ii.get_mode()) == 1)
		    {
		      nmask &= 0xff;
		      lmask &= 0xff;
		    }
		  else if (GET_MODE_SIZE(ii.get_mode()) < 4)
		    {
		      nmask &= 0xffff;
		      lmask &= 0xffff;
		    }
//printf("%d: and 0x%x, %s : 0x%x\n", index, nmask, reg_names[ii.get_dst_regno ()], lmask);
//debug(ii.get_insn());
		  if ((lmask & nmask) == lmask)
		    {
		      log ("(e) %d: eliminate superfluous 'and' to %s  %08x->%08x\n",
			   index, reg_names[ii.get_dst_regno ()], lmask, nmask);
		      delete_and_update(index);
		      ++change_count;
		    }
		}
	    }
	  continue;
	}
	
      if (REG_NREGS(ii.get_dst_reg ()) == 1
	  && is_reg_dead (ii.get_dst_regno (), index)
	  && SET_SRC(set)->volatil == 0) // keep reading volatil stuff.
	{
	  log ("(e) %d: eliminate dead assign to %s\n", index, reg_names[ii.get_dst_regno ()]);
	  delete_and_update (index);
	  ++change_count;
	  continue;
	}

      track_var * track = ii.get_track_var ();
      rtx src = SET_SRC(set);
      // check for redundant load
      if (ii.get_src_op () == 0 && ii.get_dst_reg ())
	{
	  if(!ii.is_myuse (ii.get_dst_regno ()) || ii.get_dst_regno () == ii.get_src_regno ())
	    {
	      if (track->equals (ii.get_mode(), ii.get_dst_regno (), src)
		|| (ii.get_dst_regno () == ii.get_src_regno () && (*infos)[index +1].is_def(FIRST_PSEUDO_REGISTER)))
		{
		  log ("(e) %d: eliminate redundant load to %s\n", index, reg_names[ii.get_dst_regno ()]);
		  delete_and_update (index);
		  ++change_count;
		  continue;
		}

	      if (ii.get_dst_regno () == ii.get_src_regno () && GET_MODE(ii.get_src_reg()) == GET_MODE(ii.get_dst_reg()) && is_reg_dead(FIRST_PSEUDO_REGISTER, index))
		{
		  log ("(e) %d: eliminate self load of %s\n", index, reg_names[ii.get_dst_regno ()]);
		  delete_and_update (index);
		  ++change_count;
		  continue;
		}

	      if (ii.get_src_reg () && track->equals (ii.get_mode(), ii.get_src_regno (), SET_DEST(set)))
		{
		  log ("(e) %d: eliminate redundant reverse load to %s\n", index, reg_names[ii.get_dst_regno ()]);
		  delete_and_update (index);
		  ++change_count;
		  continue;
		}
	      if (!ii.get_src_reg ())
		{
		  // is there a register holding that value?
		  int aliasRegno = track->find_alias (src);
		  if (aliasRegno >= 0 && aliasRegno != ii.get_dst_regno ())
		    {
		      log ("(e) %d: replace load with %s\n", index, reg_names[aliasRegno]);
		      if (validate_change (ii.get_insn (), &SET_SRC(set), gen_rtx_REG (ii.get_mode (), aliasRegno), 0))
			++change_count;
		      continue;
		    }
		}
	    }
	}

	// eliminate add dx,dy with dx/dy ==0
      if (ii.get_src_op () == PLUS && ii.get_dst_reg () && ii.get_src_reg() && ii.get_src_regno() <= 7)
	{
	  rtx dx = XEXP (src, 0);
	  rtx dy = XEXP (src, 1);
	  if (REG_P(dx) && REG_P(dy))
	    {
	      // dx == 0
	      rtx v = track->get(REGNO(dx));
	      if (v && CONST_INT_P(v) && INTVAL(v) == 0)
		{
		  // convert into move dy,dy
		  validate_change (ii.get_insn (), &SET_SRC(set), dy, 0);
		  log ("(e) %d: convert left add zero into move %s\n", index, reg_names[ii.get_dst_regno ()]);
		  ++change_count;
		  continue;
		}

	      // dy == 0
	      v = track->get(REGNO(dy));
	      if (v && CONST_INT_P(v) && INTVAL(v) == 0)
		{
		  // convert into move
		  validate_change (ii.get_insn (), &SET_SRC(set), dx, 0);

		  log ("(e) %d: convert right add zero into move %s\n", index, reg_names[ii.get_dst_regno ()]);
		  ++change_count;
		  continue;
		}
	    }
	}
    }
  return change_count;
}

static unsigned
opt_elim_dead_assign2 (int blocked_regno)
{
  track_regs ();

  unsigned change_count = 0;

  // same but top->down
  for (unsigned index = 0; index < infos->size () - 1; ++index)
    {
      insn_info & ii = (*infos)[index];

      if (ii.is_compare ())
	continue;

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

      if (ii.get_src_op () == 0 && ii.get_dst_reg ())
	{
	  if(!ii.is_myuse (ii.get_dst_regno ()))
	    {
	      if (!ii.get_src_reg ())
		{

		  insn_info & jj = (*infos)[index + 1];
		  // eliminate clr if the next insn makes it obsolete.
		  if (GET_MODE_SIZE(ii.get_mode()) == 4 && CONST_INT_P (SET_SRC (set)) && jj.get_dst_regno() == ii.get_dst_regno())
		    {
		      unsigned val = INTVAL (SET_SRC (set));
		      rtx jset = single_set(jj.get_insn());
		      if (!jset )
			continue;

		      track_var * track = (*infos)[index].get_track_var ();
		      if ((jj.get_mode() == QImode && val <= 0xff && (!jj.is_use_hi24(ii.get_dst_regno()) || track->getMask(ii.get_dst_regno()) <= 0xff))
		      || (jj.get_mode() == HImode && val <= 0xffff && (!jj.is_use32(ii.get_dst_regno()) || track->getMask(ii.get_dst_regno()) <= 0xffff)))
			{
//printf("%d: use24=%d, use32=%d mask=%d\n", index, jj.is_use_hi24(ii.get_dst_regno()), jj.is_use32(ii.get_dst_regno()), track->getMask(ii.get_dst_regno()));
//debug(jj.get_insn());

			  log ("(e0) %d: eliminate superfluous clear of %s\n", index, reg_names[ii.get_dst_regno ()]);
			  delete_and_update (index);
			  ++change_count;
			  continue;
			}
		    }
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

  for (unsigned i = 0; i < infos->size (); ++i)
    {
      insn_info & ii = (*infos)[i];

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
      for (; j < infos->size (); ++j)
	{
	  insn_info & jj = (*infos)[j];
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

	  // ???
	  if (jj.get_src_op () && jj.is_src_ee () && !jj.get_src_intval ())
	    continue;

	  bool j_dst = jj.is_dst_mem () && jj.get_dst_mem_mem() == 0 && (jj.has_dst_addr () || jj.get_dst_symbol ()) && !jj.has_dst_memreg ()
	      && jj.get_dst_symbol () == with_symbol;
	  bool j_src = jj.is_src_mem () && jj.get_src_mem_mem() == 0 && (jj.has_src_addr () || jj.get_src_symbol ()) && !jj.has_src_memreg ()
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
      unsigned needed = (TUNE_68040_60 || TUNE_68080) ? 10 : 2;
      if (freemask && found.size () > needed)
	{
	  unsigned regno = bit2regno (freemask);
	  /* check again. */
	  for (std::vector<unsigned>::iterator k = found.begin (); k != found.end ();)
	    {
	      insn_info & kk = (*infos)[*k];
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
      if (freemask && found.size () > needed)
	{
	  unsigned regno = bit2regno (freemask);
	  if (with_symbol)
	    log ("(b) modifying %d symbol addresses for %s using %s\n", found.size (),
		 with_symbol->u.block_sym.fld[0].rt_str, reg_names[regno]);
	  else
	    log ("(b) modifying %d absolute addresses using %s\n", found.size (), reg_names[regno]);


	  for (std::vector<unsigned>::iterator k = found.begin (); k != found.end (); ++k)
	    {
	      insn_info & kk = (*infos)[*k];
	      kk.absolute2base (regno, base, with_symbol);
	      insn_invalid_p (kk.get_insn (), 0);
	    }

	  // load base into reg
	  rtx lea;

	  if (with_symbol)
	    {
	      if (base)
		lea = gen_rtx_SET(
		    gen_raw_REG (SImode, regno),
		    gen_rtx_CONST (SImode, gen_rtx_PLUS (SImode, with_symbol, gen_rtx_CONST_INT (SImode, base))));
	      else
		lea = gen_rtx_SET(gen_raw_REG (SImode, regno), with_symbol);
	    }
	  else
	    lea = gen_rtx_SET(gen_raw_REG (SImode, regno), gen_rtx_CONST_INT (SImode, base));
	  rtx_insn * insn = emit_insn_before (lea, ii.get_insn ());
	  insn_info nn (insn);
	  nn.copy_use (ii);
	  nn.scan ();
	  nn.fledder (lea);
	  nn.mark_def (regno);
	  infos->insert (infos->begin () + i, nn);

	  /* mark until last hit is found. */
	  for (unsigned k = i + 1; k < infos->size (); ++k)
	    {
	      (*infos)[k].mark_use (regno);
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

/**
 * @param index the insn index to start with.
 * @param ii the insn_info of the auto_inc candidate.
 * @param size the size of the increment: 1,2,4,8
 * @param addend the value used in the loop: -1 to search backwards, +1 to search forwards.
 */
static int
try_auto_inc (unsigned index, insn_info & ii, rtx reg, int size, int addend)
{
  int const regno = REGNO(reg);

//      log ("starting auto_inc search for %s at %d\n", reg_names[regno], index);

  // track all fixups to modify
  std::set<unsigned> fixups;

  // all paths to check
  std::vector<unsigned> todo;

  todo.push_back (index + addend);

  std::set<unsigned> visited;

  bool last_is_add = false;
  while (todo.size () > 0)
    {
      unsigned pos = todo[todo.size () - 1];
      todo.pop_back ();

      if (pos == index)
	return 0;

      // prevent double handling
      if (visited.find (pos) != visited.end ())
	continue;

      for (; (int)pos >= 0 && pos < infos->size (); pos = pos + addend)
	{
	  visited.insert (pos);
	  insn_info & jj = (*infos)[pos];

	  // do not auto_inc over calls for d0/d1/a0/a1/a7
	  if (jj.is_call() && ((1 << regno) & ( (1<<15)|(1<<9)|(1<<8)|(1<<1)|(1<<0) )) != 0)
	    return 0;

	  // check all jumps labels for register usage
	  if (jj.is_label ())
	    {
	      if (addend < 0)
		return 0; // no labels backwards

	      if (pos > 0)
		{
		  // check previous insn, if the reg is used or defined there
		  // that label must been seen before
		  insn_info & pp = (*infos)[pos - 1];
    //	      fprintf(stderr, "regno=%d, pos=%d, used=%d, def=%d, visited=%d", regno, pos - 1, pp.is_use (regno), pp.is_def (regno), visited.find (pos - 1) != visited.end ());
    //	      debug(pp.get_insn());
		  if ((pp.is_use (regno) || pp.is_def (regno)) && visited.find (pos - 1) == visited.end ())
		    return 0;
		}

	      // jumps to here which use that register must be already visited.
	      // jumps to here which do not use that register are ok.
	      for (l2j_iterator j = label2jump->find (jj.get_insn ()->u2.insn_uid), k = j;
		  j != label2jump->end () && j->first == k->first; ++j)
		{
		  insn_info * ll = insn2info->find (j->second)->second;
		  if (ll->is_use (regno)
		      // jump from an already visited pos is ok
		      && visited.find (ll->get_index()) == visited.end ())
		    return 0;
		}
	      continue;
	    }

	  // break if no longer used
	  if (!jj.is_use (regno)) {
	      if (jj.is_def (regno))
		return 0;
	    break;
	  }

	  // abort if a parallel insn is touched.
	  if (GET_CODE(PATTERN(jj.get_insn())) == PARALLEL && (jj.is_def(regno) || jj.is_myuse(regno)))
	    return 0;

	  if (jj.in_proepi ())
	    return 0;

	  // add all labels
	  if (jj.is_jump ())
	    {
	      if (addend < 0)
		return 0; // no jumps backwards

	      for (j2l_iterator j = jump2label->find (pos), k = j; j != jump2label->end () && j->first == k->first; ++j)
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

	      // no index register
	      if (jj.get_src_mem2_reg())
		return 0;

	      if (jj.get_src_mem_addr () * addend < size)
		return 0;

	      // no inc, no double indirect
	      if (jj.get_src_mem_mem() != 0)
		return 0;

	      fix = true;
	    }
	  if (jj.get_dst_mem_regno () == regno)
	    {
	      if (jj.get_src_regno () == regno)
		return 0;

	      // no index register
	      if (jj.get_dst_mem2_reg())
		return 0;

	      if (jj.get_dst_mem_addr () * addend < size)
		return 0;

	      // no inc, no double indirect
	      if (jj.get_dst_mem_mem () != 0)
		return 0;

	      fix = true;
	    }

	  // direct add
	  if (jj.get_src_regno() == jj.get_dst_regno() && jj.get_src_op() == PLUS && jj.get_src_intval() >= size)
	    fix = true;

	  if (!fix)
	    return 0;

	  fixups.insert (pos);

	  // done if this is an add
	  if (jj.is_def (regno))
	    {
	      // new load ->invalid!
	      if (jj.get_src_op() != PLUS)
		return 0;

	      last_is_add = true;
	      break;
	    }
	}
    }

  if (!last_is_add && addend < 0)
    return 0;

  if (!fixups.size ())
    return 0;

  if (!ii.make_post_inc (regno, addend))
    return 0;

  log ("(i) auto_inc for %s at %d - %d fixups\n", reg_names[regno], index, fixups.size ());

  // fix all offsets / adds
  for (std::set<unsigned>::iterator k = fixups.begin (); k != fixups.end (); ++k)
    {
      insn_info & kk = (*infos)[*k];
//      log ("(i) fixup at %d\n", *k);
//      debug_rtx(kk.get_insn());
      kk.auto_inc_fixup (regno, size, addend);
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

  for (unsigned index = 0; index < infos->size (); ++index)
    {
      insn_info & ii = (*infos)[index];

      if (ii.in_proepi ())
	continue;

      if (!INSN_P(ii.get_insn ()))
	continue;

      if (GET_CODE(PATTERN(ii.get_insn())) == PARALLEL)
	continue;

      rtx set = single_set(ii.get_insn());
      if (!set)
	continue;

      // move.w (a0)+,a1 reads a word but writes a long...
      int dsize = GET_MODE_SIZE(ii.get_mode());
      if (dsize > 4 && !((TARGET_68881 && ii.get_mode() == DFmode) || ii.get_mode() == DImode))
        return 0;

      int ssize = dsize;
      if (ii.is_src_mem()) {
	  if (GET_CODE(SET_SRC(set)) == SIGN_EXTEND)
	    ssize /= 2;
	  else if (GET_CODE(SET_SRC(set)) == FLOAT_TRUNCATE)
	    ssize *= 2;
      }

      // neither INC or nested MEM is allowed
      // check if src is a mem which can be converted into an auto inc
      if (ii.is_src_mem() && ii.get_src_mem_regno () >= 8 && ii.get_src_mem_mem () == 0
	  && ii.get_src_mem_regno () != ii.get_dst_regno ()
	  && ii.get_src_mem_regno () != ii.get_dst_mem_regno ()
	  && ii.get_src_mem_regno () != ii.get_dst_mem2_regno ()
	  && ii.get_src_mem_regno () != ii.get_src_mem2_regno ())
	{
	  if (!ii.get_src_mem_addr ())
	    change_count += try_auto_inc (index, ii, ii.get_src_mem_reg (), ssize, 1);
	  else
	  if (ii.get_src_mem_addr () == -ssize)
	    change_count += try_auto_inc (index, ii, ii.get_src_mem_reg (), ssize, -1);
	}
      // neither INC or nested MEM is allowed
      // check if dst is a mem which can be converted into an auto inc
      if (ii.is_dst_mem() && ii.get_dst_mem_regno () >= 8 && ii.get_dst_mem_mem () == 0
	  && ii.get_src_regno () != ii.get_dst_mem_regno ()
	  && ii.get_src_mem_regno () != ii.get_dst_mem_regno ()
	  && ii.get_src_mem2_regno () != ii.get_dst_mem_regno ()
	  && ii.get_dst_mem2_regno () != ii.get_dst_mem_regno ())
	{
	  if (!ii.get_dst_mem_addr())
	    change_count += try_auto_inc (index, ii, ii.get_dst_mem_reg (), dsize, 1);
	  else
	  if (ii.get_dst_mem_addr () == -dsize)
	    change_count += try_auto_inc (index, ii, ii.get_dst_mem_reg (), dsize, -1);
	}
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
  for (unsigned index = 0; index < infos->size(); ++index)
    {
      insn_info &ii = (*infos)[index];

      // cmp #0,ax
      if (ii.is_compare() && ii.get_dst_reg() && ii.get_dst_regno() >= 8 && ii.get_dst_regno() <= 15 && !ii.is_src_mem() && ii.is_src_const() && ii.get_src_intval() == 0)
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
	      rtx dx = gen_raw_REG(SImode, regno);
	      rtx ax = gen_raw_REG(SImode, ii.get_dst_regno());
	      rtx set = gen_rtx_SET(dx, ax);
	      emit_insn_before (set, ii.get_insn());


	      rtx cmp = gen_rtx_SET(cc0_rtx,
	      				gen_rtx_COMPARE (SImode, dx, gen_rtx_CONST_INT (SImode, 0)));
	      //rtx_insn * neu =
	      emit_insn_before (cmp, ii.get_insn());
	      SET_INSN_DELETED(ii.get_insn());

	      log ("(z) cmp.w #0,%s -> move.l %s,%s\n", reg_names[ii.get_dst_regno()], reg_names[ii.get_dst_regno()], reg_names[regno]);

	      ++ change_count;
	    }
	  continue;
	}
    }
  return change_count;
}

static unsigned
opt_declear()
{
  unsigned change_count = 0;
  for (unsigned index = 0; index < infos->size(); ++index)
    {
      insn_info &ii = (*infos)[index];
      // search moveq #0,dx
      if (ii.is_dst_reg() && ii.get_dst_regno() < 8 && index + 1 < infos->size())
	{
	  rtx set = single_set(ii.get_insn());
	  if (set)
	    {
	      rtx src = SET_SRC(set);
	      if (GET_CODE(src) == CONST_INT && INTVAL(src) == 0)
		{
		  // used in next insn as src and dead?
		  insn_info & jj = (*infos)[index + 1];
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
  for (unsigned index = 1; index< infos->size(); ++index)
    {
      insn_info &ii = (*infos)[index - 1];

      // load into register and no self load?
      if (!ii.get_dst_reg() || ii.get_src_regno() == ii.get_dst_regno())
	continue;

      rtx set0 = single_set(ii.get_insn());
      if (!set0)
	continue;

      insn_info &jj = (*infos)[index ];
      rtx set = single_set(jj.get_insn());
      if (!set)
	continue;

      rtx src = SET_SRC(set);
      if (!MEM_P(src))
	continue;

      rtx reg = XEXP(src, 0);
      if (!REG_P(reg))
	continue;

      if (REGNO(reg) != (unsigned)ii.get_dst_regno() || REGNO(reg) == (unsigned)jj.get_dst_mem_regno() || !is_reg_dead(REGNO(reg), index))
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
  for (unsigned index = 0; index< infos->size(); ++index)
    {
      insn_info &ii = (*infos)[index];

      if (GET_MODE_SIZE(ii.get_mode()) > 4)
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
	  rtx set = gen_rtx_SET(gen_rtx_REG(SImode, regno), gen_rtx_CONST_INT(SImode, 0));
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
  for (unsigned index = 1; index < infos->size() - 1; ++index)
    {
      insn_info & ii = (*infos)[index];

      // only check if not in prolog and a register is set
      rtx iiset = single_set(ii.get_insn());
      if (ii.in_proepi() || ii.is_compare() || !ii.get_dst_reg() || ii.get_hard() || !iiset || ii.is_myuse (FIRST_PSEUDO_REGISTER))
	continue;

      insn_info & jj = (*infos)[index + 1];
      // don't touch compares and check for register overlap and CC use
      if (jj.is_compare() || !(jj.get_myuse() & ii.get_def()))
	continue;

      // check previous insn
      insn_info & hh = (*infos)[index - 1];
      rtx hhset = single_set(hh.get_insn());
      if (hh.is_call() || hh.is_label() || hh.is_jump() || hh.in_proepi() || hh.is_compare() || hh.get_hard() || !hhset || !hh.get_dst_reg() || hh.is_myuse (FIRST_PSEUDO_REGISTER))
	continue;

      // overlap with current insn
      if (((ii.get_myuse() | ii.get_def()) & (hh.get_myuse() | hh.get_def()) & ~(1<<(FIRST_PSEUDO_REGISTER+1))) != 0
       || rtx_equal_p(SET_SRC(iiset), SET_DEST(hhset)))
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
      if (BLOCK_FOR_INSN(head) == BLOCK_FOR_INSN(tail))
	{
	  rtx_insn * i = ii.get_insn();
	  rtx_insn * h = hh.get_insn();

	  remove_insn(i);
	  remove_insn(h);

	  add_insn_after(i, head, BLOCK_FOR_INSN(head));
	  add_insn_before(h, tail, BLOCK_FOR_INSN(tail));

	  std::swap((*infos)[index], (*infos)[index - 1]);
	  log("(n) reordered insn %d<->%d\n", index - 1, index);
	}
    }
}

/**
 * insert a moveq #0, dx .
 */
static unsigned
opt_insert_move0()
{
  std::set<unsigned> positions;

  unsigned label = 0;
  unsigned change_count = 0;
  for (unsigned index = 0, pos = 0; index< infos->size(); ++index, ++pos)
    {
      insn_info &ii = (*infos)[index];

      if (ii.is_label())
	{
	  label = index;
	  continue;
	}


      if (GET_MODE_SIZE(ii.get_mode()) >= 4)
	continue;

      int regno = ii.get_dst_regno();
      if (regno < 0 || regno > 7)
	continue;

      if (ii.is_use(regno))
	continue;

      rtx set = single_set(ii.get_insn());
      if (!set)
	continue;
      rtx src = SET_SRC (set);
      if (!MEM_P(src))
	continue;

      // this is a candidate - check if there is a AND before the next LABEL.
      // a jump to the last label exits the search.
      bool ok = true;
      insn_info * found = 0;
      int val = GET_MODE_SIZE(ii.get_mode()) == 1 ? 0xff : 0xffff;
      unsigned to = MIN(pos + 10, infos->size());
      for (unsigned pos = index + 1; ok && pos < to; ++pos)
	{
	  insn_info & pp = (*infos)[pos];
	  if (pp.is_label() || ANY_RETURN_P(PATTERN (pp.get_insn())))
	    break;

	  if (pp.is_jump())
	    {
	      for (j2l_iterator i = jump2label->find (pos), k = i; i != jump2label->end () && i->first == k->first; ++i)
		if (label == i->second)
		  {
		    ok = false;
		    break;
		  }
	      continue;
	    }

	  if (!pp.is_compare() && pp.get_dst_regno() == regno)
	    {
	      if (pp.get_src_op() == AND && pp.get_src_intval() == val)
		found = &pp;
	      break;
	    }
	}

      if (!found)
	continue;

      rtx dst = SET_DEST (set);

//      fprintf(stderr, "modesize=%d ", GET_MODE_SIZE(ii.get_mode()));
//      debug(ii.get_insn());

      if (REG_P (dst))
	{
	  // convert to strict_low_part
	  rtx slp = gen_rtx_STRICT_LOW_PART (
	  //GET_MODE (dst)
	  VOIDmode
	  , dst);
	  if (!validate_unshare_change(ii.get_insn(), &SET_DEST (set), slp, false))
	    continue;
	  log("(0) %d: to strict_low_part,%s\n", index, reg_names[regno]);
        }

      rtx nset = gen_rtx_SET(gen_rtx_REG(found->get_mode(), regno), gen_rtx_CONST_INT(found->get_mode(), 0));
      emit_insn_before (nset, ii.get_insn());
      ++change_count;

      log("(0) %d: prepend moveq #0,%s\n", index, reg_names[regno]);
      positions.insert(pos++);
    }

  return change_count;
}


void print_inline_info()
{
  unsigned count = 0;
  for (unsigned index = 0; index < infos->size(); ++index)
    {
      if (!(*infos)[index].in_proepi())
	++count;
    }

  for (unsigned m = usable_regs >> 2; m; m>>=1)
    {
      if (count && (m&1))
	--count;
    }

  printf(":bbb: inline weight = %4d\t%s\n", count, get_current_function_name ());
}

static unsigned
opt_shift (void)
{
  unsigned change_count = 0;
  for (int index = infos->size () - 2; index > 0; --index)
    {
      insn_info & ii = (*infos)[index];
      // it's a shift ?
      if (ii.get_mode() != SImode || !ii.get_dst_reg() || !(ii.get_src_op() == ASHIFT || ii.get_src_op() == ASHIFTRT || ii.get_src_op() == LSHIFTRT))
	continue;

      int dy = ii.get_dst_regno();

      // check the next insn if only a word/byte is used.
      insn_info & next = (*infos)[index + 1];
      int usedSize = next.getX(dy);
      if (usedSize >= 4)
	continue;

//      debug(ii.get_insn());
      machine_mode mode = usedSize == 1 ? QImode : HImode;
      int srcop = ii.get_src_op(); // can be changed

      // are there insns like move.l dx,dy in front of that can be changed too?
      bool reduce = false;
      for (int jndex = index - 1; jndex > 0; --jndex)
	{
	  insn_info * jj = &(*infos)[jndex];
	  if (jj->is_label())
	    break;

	  // skip unrelated insns
	  if (!jj->is_def(dy) && !jj->is_myuse(dy))
	    continue;

	  // we want sign_extend or set
	  if (!jj->is_def(dy))
	    break;

//	  debug(jj->get_insn());

	  // there might be the use of a temp register:
	  // moveq #0,dx
	  // move.w dy,dx
	  // move.l dx,dy <--- this one
	  if (jj->get_mode() == SImode && !jj->get_src_op() && jj->get_src_reg())
	    {
	      int dx = jj->get_src_regno();
	      // search the assignment for dx

	      for (int kndex = jndex - 1; kndex > 0; --kndex)
		{
		  insn_info * kk = &(*infos)[kndex];
		  if (kk->is_label())
		    break;

		  // skip unrelated insns
		  if (!kk->is_def(dx) && !kk->is_myuse(dx))
		    continue;

		  // we want sign_extend or set
		  if (!kk->is_def(dx))
		    break;

		  if (kk->get_mode() == mode && !kk->get_src_op())
		    {
		      if (srcop == ASHIFTRT)
			{
			  // we need a clr.l dx
			  insn_info * ll = &(*infos)[kndex - 1];
			  if (ll->get_dst_reg() && ll->get_dst_regno() == dx && ll->get_mode() == SImode
			      && !ll->get_src_op() && !ll->is_src_mem()
			      && ll->get_src_intval() == 0)
			    {
			      srcop = LSHIFTRT;
			      reduce = true;
			    }
			}
		      else
			reduce = true;

		      // if dx is dead after assignment to dy
		      if (reduce && is_reg_dead(dx, jndex))
			{
			  // assign src to dy unless src == dy
			  if (!kk->get_src_reg() || kk->get_src_regno() != dy)
			    {
			      rtx set = single_set(kk->get_insn());
			      rtx x = gen_rtx_SET(gen_rtx_REG (mode, dy), SET_SRC (set));
			      rtx notes = REG_NOTES (ii.get_insn());
			      rtx_insn * neu = emit_insn_before (x, kk->get_insn ());
			      REG_NOTES(neu) = notes;
			    }
			  SET_INSN_DELETED(kk->get_insn());
			  SET_INSN_DELETED(jj->get_insn());
			}
		    }
		  break;
	        }
	      break;
	    }
	  // there might be one or two sign extends
	  // ext.w dy
	  // ext.l dy
	  else if (jj->get_mode() == SImode && jj->get_src_op() == SIGN_EXTEND)
	    {
	      if (GET_MODE(jj->get_src_reg()) == mode)
		{
		  SET_INSN_DELETED(jj->get_insn());
		  reduce = true;
		}
	      else if (mode == QImode && GET_MODE(jj->get_src_reg()) == HImode)
		{
		  // check previous insn for 2nd SIGN_EXTEND
		  insn_info * ll = &(*infos)[jndex - 1];
		  if (ll->get_dst_reg() && ll->get_dst_regno() == dy
		      && ll->get_src_op() == SIGN_EXTEND
		      && GET_MODE(ll->get_src_reg()) == QImode)
		    {
		      SET_INSN_DELETED(ll->get_insn());
		      SET_INSN_DELETED(jj->get_insn());
		      reduce = true;
		    }
		}
	    }
	  // there might be an AND
	  // and.l #255,dy
	  else if (jj->get_mode() == SImode && jj->get_src_op() == AND
	      && !jj->is_src_mem())
	    {
	      int val = jj->get_src_intval();
	      if ((val == 255 && mode == QImode) || (val == 65535 && mode == HImode))
		{
		  reduce = true;
		  if (srcop == ASHIFTRT)
		    srcop = LSHIFTRT;
		  SET_INSN_DELETED(jj->get_insn());
		}
	    }
	  // move.b ..,dy or move.w ...,dy
	  else if (jj->get_mode() == mode)
	    {
	      if (srcop == ASHIFT)
		reduce = true;
	      else if (srcop == ASHIFTRT)
		{
		  // we need a clr.l dy
		  insn_info * ll = &(*infos)[jndex - 1];
		  if (ll->get_dst_reg() && ll->get_dst_regno() == dy && ll->get_mode() == SImode
		      && !ll->get_src_op() && !ll->is_src_mem()
		      && ll->get_src_intval() == 0)
		    {
		      srcop = LSHIFTRT;
		      reduce = true;
		    }
		}
	    }

	  break;
	}

      if (reduce)
	{
	  rtx op1 = XEXP(SET_SRC(PATTERN(ii.get_insn())), 1);
	  rtx r = gen_rtx_REG (mode, dy);
	  rtx shift;
	  if (srcop == ASHIFT)
	    shift = gen_rtx_ASHIFT (mode, r, op1);
	  else if (srcop == ASHIFTRT)
	    shift = gen_rtx_ASHIFTRT (mode, r, op1);
	  else
	    shift = gen_rtx_LSHIFTRT (mode, r, op1);
	  rtx x = gen_rtx_SET(r, shift);
	  rtx notes = REG_NOTES (ii.get_insn());
	  SET_INSN_DELETED(ii.get_insn());

	  rtx_insn * neu = emit_insn_before (x, ii.get_insn ());
	  REG_NOTES(neu) = notes;
	  ++change_count;

	  log ("(h) long shift replaced with shorter variant for %s\n", reg_names[ii.get_dst_regno ()]);
	}
    }
  return change_count;
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

      return TARGET_M68K && optimize > 0 && string_bbb_opts && !strchr (string_bbb_opts, '-');
    }

    virtual unsigned int
    execute (function *)
    {
      if (infos == NULL)
	{
	  infos = new std::vector<insn_info>();
	  label2jump = new std::multimap<int, rtx_insn *>();
	  jump2label = new std::multimap<unsigned, unsigned>();
	  insn2info = new std::map<rtx_insn *, insn_info *>();
	  scan_starts = new std::set<unsigned>();
	}
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
    bool do_handle_shift = strchr (string_bbb_opts, 'h') || strchr (string_bbb_opts, '+');
    bool do_autoinc = strchr (string_bbb_opts, 'i') || strchr (string_bbb_opts, '+');
    bool do_lea_mem = strchr (string_bbb_opts, 'l') || strchr (string_bbb_opts, '+');
    bool do_merge_add = strchr (string_bbb_opts, 'm') || strchr (string_bbb_opts, '+');
    bool do_pipeline = strchr (string_bbb_opts, 'n') || strchr (string_bbb_opts, '+');
    bool do_propagate_moves = strchr (string_bbb_opts, 'p') || strchr (string_bbb_opts, '+');
    bool do_bb_reg_rename = strchr (string_bbb_opts, 'r') || strchr (string_bbb_opts, '+');
    bool do_opt_strcpy = strchr (string_bbb_opts, 's') || strchr (string_bbb_opts, '+');
    bool do_opt_0 = strchr (string_bbb_opts, '0') || strchr (string_bbb_opts, '+');
    bool do_opt_final = strchr (string_bbb_opts, 'z') || strchr (string_bbb_opts, '+');

    if (be_very_verbose)
      log ("ENTER\n");

    unsigned r = update_insns ();
    if (!r)
      {
	if (do_handle_shift && opt_shift())
	  update_insns ();

	if (do_lea_mem && opt_lea_mem())
	  update_insns ();

	if (do_opt_final && opt_clear())
	  update_insns ();

	if (do_opt_0 && opt_insert_move0())
	  {XUSE('0'); update_insns(); }

	pass = 0;
	for (;;)
	  {
	    XUSE('+');
	    ++pass;
	    done = 1;
	    if (be_very_verbose)
	      log ("pass %d\n", pass);

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

	    if (do_bb_reg_rename)
	      if (opt_reg_rename ())
		{
		  XUSE('r');
		  update_insns ();
		  done = 0;
		}

	    /* convert back to clear before fixing the stack frame plus before tracking registers! */
	    if (do_opt_final && opt_declear())
	      { XUSE('f'); update_insns(); }

	    if (do_elim_dead_assign) while(opt_elim_dead_assign (STACK_POINTER_REGNUM))
	      {
		XUSE('e');
		done = 0;
		update_insns ();
	      }

	    if (do_elim_dead_assign) while(opt_elim_dead_assign2 (STACK_POINTER_REGNUM))
	      {
		XUSE('E');
		update_insns ();
	      }

	    if (do_autoinc && opt_autoinc ())
	      {XUSE('i'); done = 0; update_insns (); }

	    if (done)
	      break;
	  }

	/* convert back to clear before fixing the stack frame */
	if (do_opt_final && opt_final())
	  { XUSE('z'); update_insns(); }

	if (do_shrink_stack_frame && opt_shrink_stack_frame ())
	  { XUSE('f'); update_insns (); }

	/* elim assignments to the stack pointer last. */
	if (do_elim_dead_assign) while(opt_elim_dead_assign (FIRST_PSEUDO_REGISTER))
	  { XUSE('e'); update_insns (); }

	if (do_elim_dead_assign) while(opt_elim_dead_assign2 (FIRST_PSEUDO_REGISTER))
	  {
	    XUSE('E');
	    update_insns ();
	  }

	if (do_pipeline)
	  opt_pipeline_insns ();
      }
    if (r && be_verbose)
      log ("no bbb optimization code %d\n", r);

    if (dump_reg_track || dump_cycles || be_very_verbose || strchr (string_bbb_opts, 'X') || strchr (string_bbb_opts, 'x'))
      {
	update_insns ();
	if (dump_reg_track)
	  track_regs ();

	if (strchr (string_bbb_opts, 'X') || strchr (string_bbb_opts, 'x'))
	  dump_insns ("bbb", strchr (string_bbb_opts, 'X'));
      }

    if (be_verbose)
      print_inline_info();

    XUSE('.');
    XUSE('\n');

/*
    std::vector<insn_info>().swap(infos);
    std::multimap<int, rtx_insn *>().swap(label2jump);
    std::multimap<unsigned, unsigned>().swap(jump2label);
    std::map<rtx_insn *, insn_info *>().swap(insn2info);
    std::set<unsigned>().swap(scan_starts);
    std::vector<rtx>().swap(dstregs);
*/
    return r;
  }

}      // anon namespace

rtl_opt_pass *
make_pass_bbb_optimizations (gcc::context * ctxt)
{
  return new pass_bbb_optimizations (ctxt);
}

#define TEST(t) {int x = t(); if (!x) printf(#t " failed\n"); r &= x; }

static int
valid_address_1()
{
  rtx ad = gen_rtx_MEM(SImode, gen_rtx_REG(SImode, 6));
  return !targetm.legitimate_address_p(SImode, ad, true);
}

static int
detect_cc_use_1()
{
  rtx gt = gen_rtx_GT(QImode, cc0_rtx, GEN_INT(0));

  insn_info ii;
  ii.scan_rtx(gt);
  return ii.is_use(FIRST_PSEUDO_REGISTER);
}

int run_tests()
{
  printf("gcc-test: START\n");
  int r = 1;

  TEST(valid_address_1);
  TEST(detect_cc_use_1);

  printf("gcc-test: STOP with rc=%d\n", r);
  exit(!r);
}
