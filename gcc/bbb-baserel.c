/* Bebbo's Optimizations.
 Copyright (C) 2010-2021 Free Software Foundation, Inc.
 Copyright (C) 2017-2021 Stefan "Bebbo" Franke.

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

#include "config.h"
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
#include <genrtl.h>

namespace
{

  const pass_data pass_data_bbb_baserel =
    { RTL_PASS, /* type */
    "bebbos_baserel", /* name */
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
      return TARGET_M68K && flag_pic >= 3;
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

  static rtx picreg;
  static int cur_tmp_use;
  static rtx cur_symbol[8];
  static rtx cur_tmp_reg[8];

  int make_pic_ref(rtx_insn * insn, rtx * x, bool * use_tmp)
  {
    int r = 0;
    enum rtx_code code = GET_CODE(*x);
    if (code == SYMBOL_REF)
      {
	tree decl = SYMBOL_REF_DECL (*x);
	if (!decl)
	  return 0;
	// only handle VAR non CONST
	if (decl->base.code != VAR_DECL)
	  return 0;

	// a section means: a4 unless the section is ".datachip" ".datafast" ".datafar"
	char const * secname = DECL_SECTION_NAME(decl);
	if (secname && (
	       0 == strcmp(secname, ".datachip")
	    || 0 == strcmp(secname, ".datafast")
	    || 0 == strcmp(secname, ".datafar")))
	  return 0;

	if (secname == 0)
	  {
	    if (decl->base.constant_flag || decl->base.readonly_flag)
	      return 0;

	    // normal constants end up in text.
	    if (TREE_READONLY (decl))
	      return 0;

	    tree type = decl->decl_minimal.common.typed.type;
	    if (type->base.code == ARRAY_TYPE)
	      type = type->typed.type;
	    if (type->base.readonly_flag)
	      return 0;
	  }
	else
	  if (0 == strcmp(".text", secname))
	    return 0;

	if (secname == 0 || strcmp(".data", secname))
	  {
	    section * sec = get_variable_section(decl, false);
	    if ( (sec->common.flags & SECTION_WRITE) == 0)
	      return 0;
	  }

//	  if (decl)
//	    printf("%s: %8x %d\n", decl->decl_minimal.name->identifier.id.str, sec ? sec->common.flags : 0, ispic);

	rtx symbol = *x;

	// create the pic_ref expression
	rtx s = gen_rtx_UNSPEC (Pmode, gen_rtvec (2, *x, GEN_INT (0)),
					    UNSPEC_RELOC16);
	s = gen_rtx_CONST (Pmode, s);
	s = gen_rtx_PLUS (Pmode, picreg, s);
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

	return 1;
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
     * 5. (plus:SI (plus:SI (reg:SI 59 [ _59 ])
     *                      (reg:SI 191 [ ivtmp.364 ]))
     *             (reg:SI 300))
     *
     * again 3 registers.
     * Also move the const/plus/reg into a separate register.
     *
     */

    /* MEM can be nested inside. */
    if (GET_CODE(x) == ZERO_EXTEND || GET_CODE(x) == SIGN_EXTEND || GET_CODE(x) == STRICT_LOW_PART)
      x = XEXP(x, 0);

    rtx plus;
    if (MEM_P(x))
      plus = XEXP(x, 0);
    else
      plus = x;
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
  }

  /* Main entry point to the pass.  */
  unsigned
  pass_bbb_baserel::execute_bbb_baserel (void)
  {
    picreg = gen_rtx_REG (Pmode, PIC_REG);

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
