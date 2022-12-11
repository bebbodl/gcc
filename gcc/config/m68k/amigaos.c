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
#include "regs.h"
#include "stringpool.h"
#include "attribs.h"
#include "flags.h"
#include "expr.h"
#include "toplev.h"
#include "tm_p.h"
#include "target.h"
#include "diagnostic-core.h"
#include "langhooks.h"
#include "function.h"
#include "calls.h"
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

/*
 * begin-GG-local: explicit register specification for parameters.
 *
 * Reworked and ported to gcc-6.2.0 by Stefan "Bebbo" Franke.
 */

/**
 * Define this here and add it to tm_p -> all know the custom type and allocate/use the correct size.
 */
struct amigaos_args
{
  int num_of_regs;
  long regs_already_used;
  int last_arg_reg;
  int last_arg_len;
  tree current_param_type; /* New field: formal type of the current argument.  */
  tree fntype; /* initial function type */
};

static struct amigaos_args mycum, othercum;

bool amiga_is_ok_for_sibcall(tree decl, tree exp);
/**
 * Sibcall is only ok, if max regs d0/d1/a0 are used.
 * a1 is used for the sibcall
 * others might be trashed due to stack pop.
 */
bool amiga_is_ok_for_sibcall(tree decl, tree exp)
{
  tree fntype = decl ? TREE_TYPE (decl) : TREE_TYPE (TREE_TYPE (CALL_EXPR_FN (exp)));
  if (othercum.fntype == fntype)
    return (othercum.regs_already_used & ~0x0103) == 0;
  return false;
}

/* Argument-passing support functions.  */

/* Initialize a variable CUM of type CUMULATIVE_ARGS
 for a call to a function whose data type is FNTYPE.
 For a library call, FNTYPE is 0.  */

void
amigaos_init_cumulative_args (CUMULATIVE_ARGS *cump, tree fntype, tree decl)
{
  struct amigaos_args * cum = decl == current_function_decl ? &mycum : &othercum;
  *cump = decl == current_function_decl;
  cum->num_of_regs = amigaos_regparm > 0 ? amigaos_regparm : 0;
  DPRINTF((stderr, "0amigaos_init_cumulative_args %s %d -> %d\r\n", decl ? lang_hooks.decl_printable_name (decl, 2) : "?", *cump, cum->num_of_regs));

  /* Initialize a variable CUM of type CUMULATIVE_ARGS
   for a call to a function whose data type is FNTYPE.
   For a library call, FNTYPE is 0.  */

  cum->last_arg_reg = -1;
  cum->regs_already_used = 0;

  if (!fntype && decl)
    fntype = TREE_TYPE(decl);
// SBF: oh my ... - this caused crafted functions to lose asm parameters....
//  if (decl && DECL_ARTIFICIAL(decl))
//    fntype = 0;
  if (fntype)
    {
      tree attrs = TYPE_ATTRIBUTES(fntype);
      DPRINTF((stderr, "1amigaos_init_cumulative_args %s %d attrs: %p\r\n", decl ? lang_hooks.decl_printable_name (decl, 2) : "?", *cump, attrs));
      if (attrs)
	{
	  tree stkp = lookup_attribute ("stkparm", attrs);
	  tree fnspec = lookup_attribute ("fn spec", attrs);
	  DPRINTF((stderr, "2amigaos_init_cumulative_args %s %d stkp: %p %s\r\n", decl ? lang_hooks.decl_printable_name (decl, 2) : "?", *cump, stkp ? stkp : fnspec, IDENTIFIER_POINTER(TREE_PURPOSE(attrs))));
	  if (stkp || fnspec)
	    cum->num_of_regs = 0;
	  else
	    {
	      tree ratree = lookup_attribute ("regparm", attrs);
	      cum->num_of_regs = amigaos_regparm != 0 ? amigaos_regparm :
							AMIGAOS_DEFAULT_REGPARM;
	      if (ratree)
		{
		  int no = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(ratree)));
		  if (no > 0)
		    cum->num_of_regs = no < AMIGAOS_MAX_REGPARM ? no : AMIGAOS_MAX_REGPARM;
		}
	    }
	}
    }
  else
    /* Libcall.  */
    cum->num_of_regs = 0;

  if (cum->num_of_regs)
    {
      /* If this is a vararg call, put all arguments on stack.  */
      tree param, next_param;
      for (param = TYPE_ARG_TYPES(fntype); param; param = next_param)
	{
	  next_param = TREE_CHAIN(param);
	  if (!next_param && TREE_VALUE (param) != void_type_node)
	  cum->num_of_regs = 0;
	}
    }

#if ! defined (PCC_STATIC_STRUCT_RETURN) && defined (M68K_STRUCT_VALUE_REGNUM)
  /* If return value is a structure, and we pass the buffer address in a
   register, we can't use this register for our own purposes.
   FIXME: Something similar would be useful for static chain.  */
  if (fntype && aggregate_value_p (TREE_TYPE(fntype), fntype))
    cum->regs_already_used |= (1 << M68K_STRUCT_VALUE_REGNUM);
#endif

  if (decl && DECL_STATIC_CHAIN(decl))
    {
      rtx reg = amigaos_static_chain_rtx (decl, 0);
      if (reg)
	cum->regs_already_used |= (1 << REGNO(reg));
    }

  if (fntype)
    cum->current_param_type = TYPE_ARG_TYPES(cum->fntype = fntype);
  else
    /* Call to compiler-support function. */
    cum->current_param_type = cum->fntype = 0;
  DPRINTF((stderr, "9amigaos_init_cumulative_args %p -> %d\r\n", cum, cum->num_of_regs));
}

int
amigaos_function_arg_reg (unsigned regno)
{
  return (mycum.regs_already_used & (1 << regno)) != 0;
}

/* Update the data in CUM to advance over an argument.  */

void
amigaos_function_arg_advance (cumulative_args_t cum_v, function_arg_info const& fai)
{
  struct amigaos_args *cum = *get_cumulative_args (cum_v) ? &mycum : &othercum;
  /* Update the data in CUM to advance over an argument.  */

  DPRINTF((stderr, "amigaos_function_arg_advance1 %p\r\n", cum));

  if (cum->last_arg_reg != -1)
    {
      int count;
      for (count = 0; count < cum->last_arg_len; count++)
	cum->regs_already_used |= (1 << (cum->last_arg_reg + count));
      cum->last_arg_reg = -1;
    }

  if (cum->current_param_type)
    cum->current_param_type = TREE_CHAIN(cum->current_param_type);
}

/* Define where to put the arguments to a function.
 Value is zero to push the argument on the stack,
 or a hard register in which to store the argument.

 MODE is the argument's machine mode.
 TYPE is the data type of the argument (as a tree).
 This is null for libcalls where that information may
 not be available.
 CUM is a variable of type CUMULATIVE_ARGS which gives info about
 the preceding args and about the function being called.  */

static struct rtx_def *
_m68k_function_arg (struct amigaos_args * cum, machine_mode mode, const_tree type)
{
  DPRINTF((stderr, "m68k_function_arg numOfRegs=%d\r\n", cum ? cum->num_of_regs : 0));

  if (cum->num_of_regs)
    {
      int regbegin = -1, altregbegin = -1, len;

      /* FIXME: The last condition below is a workaround for a bug.  */
      if (TARGET_68881 && FLOAT_MODE_P(mode) &&
      GET_MODE_UNIT_SIZE (mode) <= 12 && (GET_MODE_CLASS (mode) != MODE_COMPLEX_FLOAT || mode == SCmode))
	{
	  regbegin = 16; /* FPx */
	  len = (GET_MODE_UNIT_SIZE (mode) + (UNITS_PER_WORD - 1)) / UNITS_PER_WORD;
	}
      /* FIXME: Two last conditions below are workarounds for bugs.  */
      else if (INTEGRAL_MODE_P (mode) && mode != CQImode && mode != CHImode)
	{
	  if (!type || POINTER_TYPE_P(type))
	    regbegin = 8; /* Ax */
	  else
	    regbegin = 0; /* Dx */
	  altregbegin = 8 - regbegin;
	  len = (GET_MODE_UNIT_SIZE (mode) + (UNITS_PER_WORD - 1)) / UNITS_PER_WORD;
	}

      if (regbegin != -1)
	{
	  int reg;
	  long mask;

	  look_for_reg: mask = 1 << regbegin;
	  for (reg = 0; reg < cum->num_of_regs; reg++, mask <<= 1)
	    if (!(cum->regs_already_used & mask))
	      {
		int end;
		for (end = reg; end < cum->num_of_regs && end < reg + len; end++, mask <<= 1)
		  if (cum->regs_already_used & mask)
		    break;
		if (end == reg + len)
		  {
		    cum->last_arg_reg = reg + regbegin;
		    cum->last_arg_len = len;
		    break;
		  }
	      }

	  if (reg == cum->num_of_regs && altregbegin != -1)
	    {
	      DPRINTF((stderr, "look for alt reg\n"));
	      regbegin = altregbegin;
	      altregbegin = -1;
	      goto look_for_reg;
	    }
	}

      if (cum->last_arg_reg != -1)
	{
	  DPRINTF((stderr, "-> gen_rtx_REG %d\r\n", cum->last_arg_reg));
	  return gen_rtx_REG (mode, cum->last_arg_reg);
	}
    }
  return 0;
}

/* A C expression that controls whether a function argument is passed
 in a register, and which register. */

struct rtx_def *
amigaos_function_arg (cumulative_args_t cum_v, const function_arg_info & fai)
{
	tree type = fai.type;
  DPRINTF((stderr, "amigaos_function_arg %p\r\n", cum_v.p));

  struct amigaos_args *cum = *get_cumulative_args (cum_v) ? &mycum : &othercum;

  tree asmtree = type && cum->current_param_type ? lookup_attribute("asmreg", TYPE_ATTRIBUTES(TREE_VALUE(cum->current_param_type))) : NULL_TREE;

  if (asmtree)
    {
      int i;
      cum->last_arg_reg = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(asmtree)));
      cum->last_arg_len = hard_regno_nregs(cum->last_arg_reg, fai.mode);

      for (i = 0; i < cum->last_arg_len; i++)
	{
	  if (cum->regs_already_used & (1 << (cum->last_arg_reg + i)))
	    {
	      error ("two parameters allocated for one register");
	      break;
	    }
	  cum->regs_already_used |= (1 << (cum->last_arg_reg + i));
	}
      return gen_rtx_REG (fai.mode, cum->last_arg_reg);
    }
  return _m68k_function_arg (cum, fai.mode, type);
}

void
amiga_emit_regparm_clobbers (void)
{
  for (int i = 0; i < FIRST_PSEUDO_REGISTER; ++i)
    if (mycum.regs_already_used & (1 << i))
      {
	rtx reg = gen_raw_REG (Pmode, i);
	emit_insn (gen_rtx_CLOBBER(Pmode, gen_rtx_SET(reg, gen_rtx_MEM(Pmode, reg))));
      }
}

/* Return zero if the attributes on TYPE1 and TYPE2 are incompatible,
 one if they are compatible, and two if they are nearly compatible
 (which causes a warning to be generated). */

int
amigaos_comp_type_attributes (const_tree type1, const_tree type2)
{
  DPRINTF((stderr, "amigaos_comp_type_attributes\n"));
  /* Functions or methods are incompatible if they specify mutually exclusive
   ways of passing arguments. */
  if (TREE_CODE(type1) == FUNCTION_TYPE || TREE_CODE(type1) == METHOD_TYPE)
    {
      tree attrs1 = TYPE_ATTRIBUTES(type1);

      tree asm1 = lookup_attribute("asmregs", attrs1);
      tree stack1 = lookup_attribute("stkparm", attrs1);
      tree reg1 = lookup_attribute("regparm", attrs1);

      tree attrs2 = TYPE_ATTRIBUTES(type2);

      tree asm2 = lookup_attribute("asmregs", attrs2);
      tree stack2 = lookup_attribute("stkparm", attrs2);
      tree reg2 = lookup_attribute("regparm", attrs2);

      if ((asm1 && !asm2) || (!asm1 && asm2))
	return 0;

      if (reg1)
	{
	  if (stack2)
	    return 0;

	  int no1 = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(reg1)));
	  int no2 = reg2 ? TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(reg2))) : amigaos_regparm;
	  if (no1 != no2)
	    return 0;
	}
      else if (reg2)
	{
	  if (stack1)
	    return 0;

	  int no2 = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(reg2)));
	  if (amigaos_regparm != no2)
	    return 0;
	}

      if (stack1) {
	  if (stack2)
	    return 1;
	  return amigaos_regparm  <= 0;
      }

      if (stack2)
	  return amigaos_regparm  <= 0;

      if (asm1)
	return 0 == strcmp(IDENTIFIER_POINTER(TREE_VALUE(asm1)), IDENTIFIER_POINTER(TREE_VALUE(asm2)));

    }
  else
    {
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
  return 1;
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
	  /* 'regparm' accepts one optional argument - number of registers in
	   single class that should be used to pass arguments.  */
	  if (is_attribute_p ("regparm", name))
	    {
	      DPRINTF((stderr, "regparm found\n"));

	      if (lookup_attribute ("stkparm", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("`regparm' and `stkparm' are mutually exclusive");
		  break;
		}
	      if (args && TREE_CODE (args) == TREE_LIST)
		{
		  tree val = TREE_VALUE(args);
		  DPRINTF((stderr, "regparm with val: %d\n", TREE_CODE(val)));
		  if (TREE_CODE (val) == INTEGER_CST)
		    {
		      unsigned no = TREE_INT_CST_LOW(val);
		      if (no > AMIGAOS_MAX_REGPARM)
			{
			  error ("`regparm' attribute: value %d not in [0 - %d]", no,
			  AMIGAOS_MAX_REGPARM);
			  break;
			}
		    }
		  else
		    {
		      error ("invalid argument(s) to `regparm' attribute");
		      break;
		    }
		}
	    }
	  else if (is_attribute_p ("stkparm", name))
	    {
	      if (lookup_attribute ("regparm", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("`regparm' and `stkparm' are mutually exclusive");
		  break;
		}
	    }
	  else if (is_attribute_p ("stackext", name))
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
	  else if (is_attribute_p ("asmreg", name))
	    {
	      if (args && TREE_CODE (args) == TREE_LIST)
		{
		  tree val = TREE_VALUE(args);
		  if (TREE_CODE (val) == INTEGER_CST)
		    {
		      unsigned no = TREE_INT_CST_LOW(val);
		      if (no >= 23)
			{
			  error ("`asmreg' attribute: value %d not in [0 - 23]", no);
			  break;
			}
		    }
		  else
		    {
		      error ("invalid argument(s) to `asmreg' attribute");
		      break;
		    }
		}
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
amiga_insert_attribute (tree decl, tree * attr)
{
  tree t1;
  for (t1 = *attr;t1; t1 = TREE_CHAIN (t1))
    {
  tree name = TREE_PURPOSE(t1);
  // whoops? what's that?
  if (name->base.code != IDENTIFIER_NODE)
    continue;

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
amiga_named_section (const char *name, unsigned int flags, tree decl )
{
  // only one code section - TODO: with amiga hunk this is no longer mandatory.
  if (0 == strncmp (".text", name, 5))
    name = ".text";

  if (0 == strncmp(".data", name, 5) && (!DECL_INITIAL (decl) || initializer_zerop (DECL_INITIAL (decl))))
    fprintf (asm_out_file, "\t.bss%s\n", name + 5);
  else if (0 == strncmp(".section ", name, 8) || 0 == strncmp(".text", name, 5) || 0 == strncmp(".data", name, 5) || 0 == strncmp(".bss", name, 4))
    fprintf (asm_out_file, "\t%s\n", name);
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

rtx
amigaos_struct_value_rtx (tree fntype, int incoming ATTRIBUTE_UNUSED)
{
    return gen_rtx_REG (Pmode, M68K_STRUCT_VALUE_REGNUM);
}

rtx
amigaos_static_chain_rtx (const_tree decl, bool incoming ATTRIBUTE_UNUSED)
{
  if (!decl || !DECL_STATIC_CHAIN(decl))
    return 0;

  unsigned used = 0;
  tree fntype = TREE_TYPE(decl);
  if (fntype)
    for (tree current_param_type = TYPE_ARG_TYPES(fntype); current_param_type; current_param_type = TREE_CHAIN(current_param_type))
      {
	tree asmtree = TYPE_ATTRIBUTES(TREE_VALUE(current_param_type));
	if (!asmtree || strcmp ("asmreg", IDENTIFIER_POINTER(TREE_PURPOSE(asmtree))))
	  continue;

	unsigned regno = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(asmtree)));
	used |= 1 << regno;
      }

  if (!(used & (1 << 9)))
    return gen_rtx_REG (Pmode, 9);
  if (!(used & (1 << 10)))
    return gen_rtx_REG (Pmode, 10);
  if (!(used & (1 << 11)))
    return gen_rtx_REG (Pmode, 11);
  if (!(used & (1 << 14)))
    return gen_rtx_REG (Pmode, 14);

  return 0;
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
	      if (!REG_P(reg))
		return true;

	      return false;
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
amigaos_alternate_frame_setup_f (int fsize)
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
amigaos_alternate_frame_setup (int fsize)
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
