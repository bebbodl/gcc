/* Configuration for GNU C-compiler for m68k Amiga, running AmigaOS.
 Copyright (C) 1992, 1993, 1994, 1995, 1996, 1997, 1998, 2003
 Free Software Foundation, Inc.
 Contributed by Markus M. Wild (wild@amiga.physik.unizh.ch).
 Heavily modified by Kamil Iskra (iskra@student.uci.agh.edu.pl).

 This file is part of GCC.

 GCC is free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2, or (at your option)
 any later version.

 GCC is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with GCC; see the file COPYING.  If not, write to
 the Free Software Foundation, 59 Temple Place - Suite 330,
 Boston, MA 02111-1307, USA.  */

//work without flag_writable_strings which is not in GCC4
#define REGPARMS_68K 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "output.h"
#include "tree.h"
#include "attribs.h"
#include "flags.h"
#include "expr.h"
#include "toplev.h"
#include "tm_p.h"
#include "target.h"
#include "diagnostic-core.h"
#include "langhooks.h"
#include "function.h"
#include "stor-layout.h"
#include "config/m68k/amigaos.h"

//#define MYDEBUG 1
#ifdef MYDEBUG
#define DPRINTF(x) fprintf x;
#else
#define DPRINTF(x)
#endif

//int amiga_declare_object;

#if 0

//----- from 68k.c start

/* Stack checking and automatic extension support.  */

void
amigaos_prologue_begin_hook (FILE *stream, int fsize)
  {
    if (TARGET_STACKCHECK)
      {
	if (fsize < 256)
	asm_fprintf (stream, "\tcmpl %s,%Rsp\n"
	    "\tjcc 0f\n"
	    "\tjra %U__stkovf\n"
	    "\t0:\n",
	    (flag_pic == 3 ? "a4@(___stk_limit:W)" :
		(flag_pic == 4 ? "a4@(___stk_limit:L)" :
		    "___stk_limit")));
	else
	asm_fprintf (stream, "\tmovel %I%d,%Rd0\n\tjbsr %U__stkchk_d0\n",
	    fsize);
      }
  }


//static rtx
//gen_stack_management_call (rtx stack_pointer, rtx arg, const char *func)
//{
//  rtx call_insn, call, seq, name;
//  start_sequence ();
//
//  /* Move arg to d0.  */
//  emit_move_insn (gen_rtx_REG (SImode, 0), arg);
//
//  /* Generate the function reference.  */
//  name = gen_rtx_SYMBOL_REF (Pmode, func);
//  SYMBOL_REF_FLAG (name) = 1;
//  /* If optimizing, put it in a psedo so that several loads can be merged
//     into one.  */
//  if (optimize && ! flag_no_function_cse)
//    name = copy_to_reg (name);
//
//  /* Generate the function call.  */
//  call = gen_rtx_CALL (VOIDmode, gen_rtx_MEM (FUNCTION_MODE, name),
//		  const0_rtx);
//  /* If we are doing stack extension, notify about the sp change.  */
//  if (stack_pointer)
//    call = gen_rtx_SET (VOIDmode, stack_pointer, call);
//
//  /* Generate the call instruction.  */
//  call_insn = emit_call_insn (call);
//  /* Stack extension does not change memory in an unpredictable way.  */
//  RTL_CONST_OR_PURE_CALL_P (call_insn) = 1;
//  /* We pass an argument in d0.  */
//  CALL_INSN_FUNCTION_USAGE (call_insn) = gen_rtx_EXPR_LIST (VOIDmode,
//	gen_rtx_USE (VOIDmode, gen_rtx_REG (SImode, 0)), 0);
//
//  seq = get_insns ();
//  end_sequence ();
//  return seq;
//}
//
//rtx
//gen_stack_cleanup_call (rtx stack_pointer, rtx sa)
//{
//  return gen_stack_management_call (stack_pointer, sa, "__move_d0_sp");
//}
//
//void
//amigaos_alternate_allocate_stack (rtx *operands)
//{
//  if (TARGET_STACKEXTEND)
//    emit_insn (gen_stack_management_call (stack_pointer_rtx, operands[1],
//					  "__sub_d0_sp"));
//  else
//    {
//      if (TARGET_STACKCHECK)
//	emit_insn (gen_stack_management_call (0, operands[1], "__stkchk_d0"));
//      anti_adjust_stack (operands[1]);
//    }
//  emit_move_insn (operands[0], virtual_stack_dynamic_rtx);
//}
#endif

/* Return zero if the attributes on TYPE1 and TYPE2 are incompatible,
 one if they are compatible, and two if they are nearly compatible
 (which causes a warning to be generated). */

int
amigaos_comp_type_attributes (const_tree type1, const_tree type2)
{
  DPRINTF((stderr, "m68k_comp_type_attributes\n"));
  tree attrs1 = TYPE_ATTRIBUTES(type1);

  tree chip1 = lookup_attribute("chip", attrs1);
  tree fast1 = lookup_attribute("fast", attrs1);
  tree far1 = lookup_attribute("far", attrs1);

  tree attrs2 = TYPE_ATTRIBUTES(type2);

  tree chip2 = lookup_attribute("chip", attrs2);
  tree fast2 = lookup_attribute("fast", attrs2);
  tree far2 = lookup_attribute("far", attrs2);

  if (chip1)
    return chip2 && !fast2 && !far2;

  if (fast1)
    return !chip2 && fast2 && !far2;

  if (far1)
    return !chip2 && !fast2 && far2;

  return !chip2 && !fast2 && !far2;
}
/* end-GG-local */

/* Handle a regparm, stkparm, saveds attribute;
 arguments as in struct attribute_spec.handler.  */
tree
amigaos_handle_type_attribute (tree *node, tree name, tree args, int flags ATTRIBUTE_UNUSED, bool *no_add_attrs)
{
  tree nnn = *node;
  do
    { // while (0);
      DPRINTF((stderr, "%p with treecode %d\n", node, TREE_CODE(nnn)));
      if (TREE_CODE (nnn) == FUNCTION_DECL || TREE_CODE (nnn) == FUNCTION_TYPE || TREE_CODE (nnn) == METHOD_TYPE)
	{
	  if (is_attribute_p ("stackext", name))
	    {
	      if (lookup_attribute ("interrupt", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("`stackext' and `interrupt' are mutually exclusive");
		  break;
		}
	    }
	  else if (is_attribute_p ("saveds", name))
	    {
	      if (flag_pic < 3)
		{
		  warning (OPT_Wattributes, "`%s' attribute is only usable with fbaserel", IDENTIFIER_POINTER(name));
		}
	      else
	      if (flag_resident)
		{
		  error ("`saveds' can't be used with resident!\n");
		}
	    }
	  else if (is_attribute_p ("entrypoint", name))
	    {
	      if (lookup_attribute ("saveallregs", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("`entrypoint' and `saveallregs' are mutually exclusive");
		  break;
		}
	    }
	  else if (is_attribute_p ("saveallregs", name))
	    {
	      if (lookup_attribute ("entrypoint", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("`entrypoint' and `saveallregs' are mutually exclusive");
		  break;
		}
	    }
	  else
	    {
	      warning (OPT_Wattributes, "`%s' attribute only applies to data", IDENTIFIER_POINTER(name));
	    }
	}
      else
	{
	  if (is_attribute_p ("chip", name) || is_attribute_p ("fast", name) || is_attribute_p ("far", name))
	    {
	      // OK
	    }
	  else
	    {
	      warning (OPT_Wattributes, "`%s' attribute only applies to functions", IDENTIFIER_POINTER(name));
	    }
	}
      return NULL_TREE ;
    }
  while (0);
  // error case
  *no_add_attrs = true;
  return NULL_TREE ;
}

#define AMIGA_CHIP_SECTION_NAME ".datachip"
#define AMIGA_FAST_SECTION_NAME ".datafast"
#define AMIGA_FAR_SECTION_NAME  ".datafar"

void
amigaos_insert_attribute (tree decl, tree * attr)
{
  tree t1;
  for (t1 = *attr;t1; t1 = TREE_CHAIN (t1))
    {
  tree name = TREE_PURPOSE(t1);

  if (is_attribute_p("chip", name) || is_attribute_p("far", name) || is_attribute_p("fast", name))
    {
      if (TREE_TYPE(decl)->base.code == VAR_DECL)
	{
	  error ("`%s' attribute can only be specified for variables", IDENTIFIER_POINTER(name));
	  return;
	}

      if (! TREE_STATIC (decl) && ! DECL_EXTERNAL (decl))
	{
	  error ("`%s' attribute cannot be specified for local variables", IDENTIFIER_POINTER(name));
	  return;
	}

      char const * section_name;
      if (is_attribute_p("chip", name))
	section_name = AMIGA_CHIP_SECTION_NAME;
      else if (is_attribute_p("fast", name))
	section_name = AMIGA_FAST_SECTION_NAME;
      else if (is_attribute_p("far", name))
	section_name = AMIGA_FAR_SECTION_NAME;


      /* The decl may have already been given a section attribute from
	     a previous declaration.  Ensure they match.  */
      if (DECL_SECTION_NAME (decl) == NULL)
	set_decl_section_name(decl, section_name);
      else if (strcmp (DECL_SECTION_NAME (decl), section_name) )
	{
	  error_at (DECL_SOURCE_LOCATION(decl),
		  "`%s' attribute conflicts with previous declaration", IDENTIFIER_POINTER(name));
	}
    }
  else
    {
//      warning (OPT_Wattributes, "`%s' attribute unknown", IDENTIFIER_POINTER(name));
    }
    }
}

/* Output assembly to switch to section NAME with attribute FLAGS.  */
#ifndef TARGET_AMIGAOS_VASM
extern void
amiga_named_section (const char *name, unsigned int flags ATTRIBUTE_UNUSED, tree decl )
{
  // put startup/exit into .text - otherwise stabs for DTOR will fail
  if (0 == strncmp (".text.startup", name, 13) || 0 == strncmp (".text.exit", name, 10))
    name = ".text";

  if (0 == strncmp(".data", name, 5))
    {
     if (!DECL_INITIAL (decl) || initializer_zerop (DECL_INITIAL (decl)))
      {
	extern section * in_section;
	fprintf (asm_out_file, "\t.section .bss%s\n", name + 5);
      }
     else
       fprintf (asm_out_file, "\t.section %s\n", name);

     if (strstr(name, "chip") || strstr(name, "fast") || strstr(name, "far"))
       in_section = NULL;
    }
//  else if (0 == strncmp(".section ", name, 8) || 0 == strncmp(".text", name, 5) || 0 == strncmp(".data", name, 5) || 0 == strncmp(".bss", name, 4))
//    fprintf (asm_out_file, "\t%s\n", name);
  else
    fprintf (asm_out_file, "\t.section %s\n", name);
}
#else
extern void
amiga_named_section (const char *name, unsigned int flags, tree decl ATTRIBUTE_UNUSED)
  {
    if (0 == strncmp(".text", name, 5))
      name = ".text,code";

    if (0 == strncmp("section ", name, 8))
      {
	fprintf (asm_out_file, "\t%s\n", name);
      }
    else
      {
	if (0 == strncmp(".data", name, 5) && (!DECL_INITIAL (decl) || initializer_zerop (DECL_INITIAL (decl))))
	  {
	  if (0 == strncmp(".data_chip", name, 10))
	    {
	      fprintf (asm_out_file, "\tsection .bss_chip,bss,chip\n");
	    }
	  else
	    {
	      fprintf (asm_out_file, "\tsection .bss%s%s,bss\n", name[5]==0 ? "" : "_", name + 5);
	    }
	  }
	else
	  {
	    if (0 == strncmp(".datafar", name, 8))
	      {
		fprintf (asm_out_file, "\tsection .data_far,data\n");
	      }
	    else if (0 == strncmp(".datachip", name, 9))
	      {
		fprintf (asm_out_file, "\tsection .data_chip,data,chip\n");
	      }
	    else if (0 == strncmp(".bsschip", name, 8))
	      {
		fprintf (asm_out_file, "\tsection .bss_chip,bss,chip\n");
	      }
	    else
	      {
		fprintf (asm_out_file, "\tsection %s\n", name);
	      }
	  }
      }
  }
#endif

/* Baserel support.  */

/**
 * Does x reference the pic_reg and is const or plus?
 */
static int
_amiga_is_const_pic_ref (const_rtx x)
{
  while (GET_CODE(x) == CONST)
    x = XEXP(x, 0);

  if (GET_CODE(x) != PLUS)
    return false;

  if (GET_CODE(XEXP(x, 0)) == CONST_INT)
    return _amiga_is_const_pic_ref(XEXP(x, 1));
  if (GET_CODE(XEXP(x, 1)) == CONST_INT)
    return _amiga_is_const_pic_ref(XEXP(x, 0));

  rtx r = XEXP(x,0);
  rtx u = XEXP(x,1);

  if (!REG_P(r) || REGNO(r) != PIC_OFFSET_TABLE_REGNUM )
    return false;

  for (;;)
    {
      while (GET_CODE(u) == CONST)
	u = XEXP(u, 0);
      if (GET_CODE(u) != PLUS)
	break;

      if (GET_CODE(XEXP(u, 1)) != CONST_INT)
	return false;
      u = XEXP(u, 0);
    }

  return GET_CODE(u) == UNSPEC;
}

int
amiga_is_const_pic_ref (const_rtx cnst)
{
  if (flag_pic < 3)
    return false;
  int r = _amiga_is_const_pic_ref (cnst);
//  fprintf(stderr, r ? "valid pic: " : "invalid pic: ");
//  debug_rtx(cnst);
  return r;
}


/* Does operand (which is a symbolic_operand) live in text space? If
 so SYMBOL_REF_FLAG, which is set by ENCODE_SECTION_INFO, will be true.

 This function is used in base relative code generation. */

int
read_only_operand (rtx operand)
{
  if (GET_CODE (operand) == CONST)
    operand = XEXP(XEXP (operand, 0), 0);
  if (GET_CODE (operand) == SYMBOL_REF)
    return SYMBOL_REF_FLAG (operand) || CONSTANT_POOL_ADDRESS_P(operand);
  return 1;
}

/**
 * Necessary to block some funny invalid combinations if baserel is used:
 *
(const:SI (minus:SI (neg:SI (reg:SI 12 a4))
      (const:SI (plus:SI (unspec:SI [
		      (symbol_ref:SI ("xyz") <var_decl 0xffcf0000 xyz>)
		      (const_int 0 [0])
		  ] 6)

(plus:SI (reg:SI 10 a2)
    (const:SI (minus:SI (neg:SI (reg:SI 12 a4))
	    (const:SI (plus:SI (unspec:SI [
			    (symbol_ref:SI ("xyz") <var_decl 0xffcf0000 xyz>)
			    (const_int 0 [0])
			] 6)
		    (const_int 1234 [0xe00]))))))) xyz.c:41 465 {*lea}

 */
bool
amigaos_legitimate_src (rtx src)
{
  if (flag_pic < 3)
    return true;

  if (MEM_P(src))
    {
      rtx x = XEXP(src, 0);
      if (GET_CODE(x) == PLUS || GET_CODE(x) == MINUS) {
	  if (amiga_is_const_pic_ref(XEXP(x, 0))
	      || amiga_is_const_pic_ref(XEXP(x, 1)))
	    return false;
      }
      return true;
    }

  if (GET_CODE(src) == PLUS || GET_CODE(src) == MINUS)
    {
      rtx x = XEXP(src, 0);
      rtx y = XEXP(src, 1);

      /** handled in print_operand_address(...) */
      if (amiga_is_const_pic_ref(x))
	  return GET_CODE(y) == CONST_INT;

      return amigaos_legitimate_src(x) && amigaos_legitimate_src(y) && !amiga_is_const_pic_ref(y);
    }

  if (GET_CODE(src) == CONST)
    {
      rtx op = XEXP(src, 0);
      if (GET_CODE(op) == MINUS || GET_CODE(op) == PLUS)
	{
	  rtx x = XEXP(op, 0);
	  if (GET_CODE(x) == NOT || GET_CODE(x) == NEG || GET_CODE(x) == SIGN_EXTEND)
	    {
	      rtx reg = XEXP(x, 0);
	      return CONST_INT_P (reg);
	    }
	}

      if (GET_CODE(op) == UNSPEC)
	return false;
    }

  return true;
}

void
amigaos_restore_a4 (void)
  {
    if (flag_pic >= 3 && !flag_resident)
      {
	tree attrs = TYPE_ATTRIBUTES (TREE_TYPE (current_function_decl));
	tree attr = lookup_attribute ("saveds", attrs);
	if (attr || TARGET_RESTORE_A4 || TARGET_ALWAYS_RESTORE_A4)
	  {
	    rtx a4 = gen_rtx_ASM_INPUT_loc(VOIDmode, "\tjsr ___restore_a4", DECL_SOURCE_LOCATION (current_function_decl));
	    a4->volatil = 1;
	    emit_insn(a4);
	  }
      }
  }

void
amigaos_alternate_frame_setup_f (int fsize ATTRIBUTE_UNUSED)
  {
#if 0
    if (fsize < 128)
    asm_fprintf (stream, "\tcmpl %s,%Rsp\n"
	"\tjcc 0f\n"
	"\tmoveq %I%d,%Rd0\n"
	"\tmoveq %I0,%Rd1\n"
	"\tjbsr %U__stkext_f\n"
	"0:\tlink %Ra5,%I%d:W\n",
	(flag_pic == 3 ? "a4@(___stk_limit:W)" :
	    (flag_pic == 4 ? "a4@(___stk_limit:L)" :
		"___stk_limit")),
	fsize, -fsize);
    else
    asm_fprintf (stream, "\tmovel %I%d,%Rd0\n\tjbsr %U__link_a5_d0_f\n",
	fsize);
#endif
  }

void
amigaos_alternate_frame_setup (int fsize ATTRIBUTE_UNUSED)
  {
#if 0
    if (!fsize)
    asm_fprintf (stream, "\tcmpl %s,%Rsp\n"
	"\tjcc 0f\n"
	"\tmoveq %I0,%Rd0\n"
	"\tmoveq %I0,%Rd1\n"
	"\tjbsr %U__stkext_f\n"
	"0:\n",
	(flag_pic == 3 ? "a4@(___stk_limit:W)" :
	    (flag_pic == 4 ? "a4@(___stk_limit:L)" :
		"___stk_limit")));
    else if (fsize < 128)
    asm_fprintf (stream, "\tcmpl %s,%Rsp\n"
	"\tjcc 0f\n"
	"\tmoveq %I%d,%Rd0\n"
	"\tmoveq %I0,%Rd1\n"
	"\tjbsr %U__stkext_f\n"
	"0:\taddw %I%d,%Rsp\n",
	(flag_pic == 3 ? "a4@(___stk_limit:W)" :
	    (flag_pic == 4 ? "a4@(___stk_limit:L)" :
		"___stk_limit")),
	fsize, -fsize);
    else
    asm_fprintf (stream, "\tmovel %I%d,%Rd0\n\tjbsr %U__sub_d0_sp_f\n",
	fsize);
#endif
  }

#if 0
extern bool debug_recog(char const * txt, int which_alternative, int n, rtx * operands)
{
  fprintf(stderr, "%s: %d ", txt, which_alternative);
  for (int i = 0; i < n; ++i)
    print_rtl(stderr, operands[i]);
  fprintf(stderr, "\n--\n");
  return true;
}
#endif

int amiga_is_far_symbol(const_rtx x)
{
	if (GET_CODE(x) != SYMBOL_REF)
		return 0;

	tree decl = SYMBOL_REF_DECL(x);
	if (!decl)
		return 0;

	if (decl && (decl->base.code == VAR_DECL || decl->base.code == CONST_DECL) && DECL_SECTION_NAME(decl))
		return 1;

	return 0;
}
