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
#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "output.h"
#include "tree.h"
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
#include "stor-layout.h"
#include "calls.h"

//#define MYDEBUG 1
#ifdef MYDEBUG
#define DPRINTF(x) fprintf x;
#else
#define DPRINTF(x)
#endif

/*
 * begin-GG-local: explicit register specification for parameters.
 *
 * Reworked and ported to gcc-6.2.0 by Stefan "Bebbo" Franke.
 */

extern rtx
m68k_static_chain_rtx(const_tree fntype,
			       bool incoming ATTRIBUTE_UNUSED);

/**
 * Define this here and add it to tm_p -> all know the custom type and allocate/use the correct size.
 */
struct m68k_args
{
  int num_of_regs;
  long regs_already_used;
  int last_arg_reg;
  int last_arg_len;
  tree current_param_type; /* New field: formal type of the current argument.  */
  tree fntype; /* initial function type */
};

static struct m68k_args mycum, othercum;

bool m68k_is_ok_for_sibcall(tree decl, tree exp);
/**
 * Sibcall is only ok, if max regs d0/d1/a0 are used.
 * a1 is used for the sibcall
 * others might be trashed due to stack pop.
 */
bool m68k_is_ok_for_sibcall(tree decl, tree exp)
{
  tree fntype = decl ? TREE_TYPE (decl) : TREE_TYPE (TREE_TYPE (CALL_EXPR_FN (exp)));
  if (othercum.fntype == fntype)
    return (othercum.regs_already_used & ~0x010103) == 0;
  return false;
}

/* Argument-passing support functions.  */

/* Initialize a variable CUM of type CUMULATIVE_ARGS
 for a call to a function whose data type is FNTYPE.
 For a library call, FNTYPE is 0.  */

void
m68k_init_cumulative_args (CUMULATIVE_ARGS *cump, tree fntype, tree decl)
{
  struct m68k_args * cum = decl == current_function_decl ? &mycum : &othercum;
  *cump = decl == current_function_decl;
  if (sas_regparm)
    m68k_regparm = 2;
  cum->num_of_regs = m68k_regparm > 0 ? m68k_regparm : 0;
  DPRINTF((stderr, "0m68k_init_cumulative_args %s %d -> %d\r\n", decl ? lang_hooks.decl_printable_name (decl, 2) : "?", *cump, cum->num_of_regs));

  /* Initialize a variable CUM of type CUMULATIVE_ARGS
   for a call to a function whose data type is FNTYPE.
   For a library call, FNTYPE is 0.  */

  cum->last_arg_reg = -1;
  cum->regs_already_used = 0;

  if (!fntype && decl)
    fntype = TREE_TYPE(decl);
// SBF: oh my ... - this caused crafted functions to lose asm parameters....
// but it was needed for memset - uh  oh - doh - use virtual instead
  if (decl && decl->decl_common.virtual_flag)
    fntype = NULL;

  if (decl && fndecl_built_in_p(decl))
    fntype = NULL;

  tree attrs = NULL;
  if (fntype)
    {
      attrs = TYPE_ATTRIBUTES(fntype);
      DPRINTF((stderr, "1m68k_init_cumulative_args %s %d attrs: %p\r\n", decl ? lang_hooks.decl_printable_name (decl, 2) : "?", *cump, attrs));
      if (attrs)
	{
	  tree stkp = lookup_attribute ("stkparm", attrs);
	  tree fnspec = lookup_attribute ("fn spec", attrs);
	  DPRINTF((stderr, "2m68k_init_cumulative_args %s %d stkp: %p %s\r\n", decl ? lang_hooks.decl_printable_name (decl, 2) : "?", *cump, stkp ? stkp : fnspec, IDENTIFIER_POINTER(TREE_PURPOSE(attrs))));
	  if (stkp || fnspec)
	    cum->num_of_regs = 0;
	  else
	    {
	      tree ratree = lookup_attribute ("regparm", attrs);
	      cum->num_of_regs = m68k_regparm != 0 ? m68k_regparm :
							M68K_DEFAULT_REGPARM;
	      if (ratree)
		{
		  int no = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(ratree)));
		  if (no > 0)
		    cum->num_of_regs = no < M68K_MAX_REGPARM ? no : M68K_MAX_REGPARM;
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
   register, we cannot use this register for our own purposes.
   FIXME: Something similar would be useful for static chain.  */
  if (fntype && aggregate_value_p (TREE_TYPE(fntype), fntype))
    cum->regs_already_used |= (1 << M68K_STRUCT_VALUE_REGNUM);
#endif

  if (fntype && fntype->base.code == FUNCTION_DECL && DECL_STATIC_CHAIN(fntype))
    {
      rtx reg = m68k_static_chain_rtx (decl, 0);
      if (reg)
	cum->regs_already_used |= (1 << REGNO(reg));
    }

  if (fntype)
    cum->current_param_type = TYPE_ARG_TYPES(cum->fntype = fntype);
  else
    /* Call to compiler-support function. */
    cum->current_param_type = cum->fntype = 0;
  DPRINTF((stderr, "9m68k_init_cumulative_args %p -> %d\r\n", cum, cum->num_of_regs));
}

int
m68k_function_arg_reg (unsigned regno)
{
  return (mycum.regs_already_used & (1 << regno)) != 0;
}

rtx
m68k_function_value(const_tree type, const_tree fn_decl_or_type, bool outgoing)
{
  machine_mode mode = TYPE_MODE(type);
  if (!fn_decl_or_type)
    fn_decl_or_type = outgoing ? mycum.fntype : othercum.fntype;
  if (fn_decl_or_type && TARGET_68881 && (mode == DFmode || mode == SFmode))
    return gen_rtx_REG (mode, FP0_REG);
  return gen_rtx_REG (mode, D0_REG);
}

bool
m68k_function_value_regno_p(unsigned regno) {
  if (TARGET_68881 && mycum.fntype)
	return regno == FP0_REG;
  return regno == D0_REG;
}


/* Update the data in CUM to advance over an argument.  */

void m68k_function_arg_advance (cumulative_args_t cum_v,
				       const function_arg_info & ai)
{
  struct m68k_args *cum = *get_cumulative_args (cum_v) ? &mycum : &othercum;
  /* Update the data in CUM to advance over an argument.  */

  DPRINTF((stderr, "m68k_function_arg_advance1 %p\r\n", cum));

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
_m68k_function_arg (struct m68k_args * cum, machine_mode mode, const_tree type)
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
	  len = GET_MODE_NUNITS(mode);
	}
      /* FIXME: Two last conditions below are workarounds for bugs.  */
      else if (INTEGRAL_MODE_P (mode) && mode != CQImode && mode != CHImode)
	{
	  if (!type || POINTER_TYPE_P(type))
	    regbegin = 8; /* Ax */
	  else
	    regbegin = 0; /* Dx */

	  if (!sas_regparm)
	    altregbegin = 8 - regbegin;
	  len = (GET_MODE_SIZE (mode) + (UNITS_PER_WORD - 1)) / UNITS_PER_WORD;
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

rtx m68k_function_arg (cumulative_args_t cum_v, const function_arg_info & ai)
{
  DPRINTF((stderr, "m68k_function_arg %p\r\n", cum_v.p));

  struct m68k_args *cum = *get_cumulative_args (cum_v) ? &mycum : &othercum;

  tree asmtree = ai.type && cum->current_param_type ? lookup_attribute("asmreg", TYPE_ATTRIBUTES(TREE_VALUE(cum->current_param_type))) : NULL_TREE;

  if (asmtree)
    {
      int i;
      cum->last_arg_reg = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(asmtree)));
      cum->last_arg_len = ai.mode == DImode ? 2 : 1;

      for (i = 0; i < cum->last_arg_len; i++)
	{
	  if (cum->regs_already_used & (1 << (cum->last_arg_reg + i)))
	    {
	      error ("two parameters allocated for one register");
	      break;
	    }
	  cum->regs_already_used |= (1 << (cum->last_arg_reg + i));
	}
      return gen_rtx_REG (ai.mode, cum->last_arg_reg);
    }
  return _m68k_function_arg (cum, ai.mode, ai.type);
}

void
m68k_emit_regparm_clobbers (void)
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
m68k_comp_type_attributes (const_tree type1, const_tree type2)
{
  DPRINTF((stderr, "m68k_comp_type_attributes\n"));
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
	  int no2 = reg2 ? TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(reg2))) : m68k_regparm;
	  if (no1 != no2)
	    return 0;
	}
      else if (reg2)
	{
	  if (stack1)
	    return 0;

	  int no2 = TREE_INT_CST_LOW(TREE_VALUE(TREE_VALUE(reg2)));
	  if (m68k_regparm != no2)
	    return 0;
	}

      if (stack1) {
	  if (stack2)
	    return 1;
	  return m68k_regparm  <= 0;
      }

      if (stack2)
	  return m68k_regparm  <= 0;

      if (asm1)
	return 0 == strcmp(IDENTIFIER_POINTER(TREE_VALUE(asm1)), IDENTIFIER_POINTER(TREE_VALUE(asm2)));

    }
  return 1;
}
/* end-GG-local */

/* Handle a regparm, stkparm, saveds attribute;
 arguments as in struct attribute_spec.handler.  */
tree
m68k_handle_type_attribute (tree *node, tree name, tree args, int flags ATTRIBUTE_UNUSED, bool *no_add_attrs)
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
		  error ("%'regparm%' and %'stkparm%' aka %'__stdargs%' are mutually exclusive");
		  break;
		}
	      if (args && TREE_CODE (args) == TREE_LIST)
		{
		  tree val = TREE_VALUE(args);
		  DPRINTF((stderr, "regparm with val: %d\n", TREE_CODE(val)));
		  if (TREE_CODE (val) == INTEGER_CST)
		    {
		      unsigned no = TREE_INT_CST_LOW(val);
		      if (no > M68K_MAX_REGPARM)
			{
			  error ("%'regparm%' attribute: value %d not in [0 - %d]", no,
			  M68K_MAX_REGPARM);
			  break;
			}
		    }
		  else
		    {
		      error ("invalid argument(s) to %'regparm%' attribute");
		      break;
		    }
		}
	    }
	  else if (is_attribute_p ("stkparm", name))
	    {
	      if (lookup_attribute ("regparm", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("%'regparm%' and %'stkparm%' aka %'__stdargs%' are mutually exclusive");
		  break;
		}
	    }
	  else
	    {
	      warning (OPT_Wattributes, "%'%s%' attribute only applies to data", IDENTIFIER_POINTER(name));
	    }
	}
      else
	{
	  if (is_attribute_p ("asmreg", name))
	    {
	      if (args && TREE_CODE (args) == TREE_LIST)
		{
		  tree val = TREE_VALUE(args);
		  if (TREE_CODE (val) == INTEGER_CST)
		    {
		      unsigned no = TREE_INT_CST_LOW(val);
		      if (no >= 23)
			{
			  error ("%'asmreg%' attribute: value %d not in [0 - 23]", no);
			  break;
			}
		    }
		  else
		    {
		      error ("invalid argument(s) to %'asmreg%' attribute");
		      break;
		    }
		}
	    }
	  else
	    {
	      warning (OPT_Wattributes, "%'%s%' attribute only applies to functions", IDENTIFIER_POINTER(name));
	    }
	}
      return NULL_TREE ;
    }
  while (0);
  // error case
  *no_add_attrs = true;
  return NULL_TREE ;
}

rtx
m68k_static_chain_rtx (const_tree decl, bool incoming ATTRIBUTE_UNUSED)
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
