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
#include "config/m68k/amigaos.h"

//#define MYDEBUG 1
#ifdef MYDEBUG
#define DPRINTF(x) fprintf x;
#else
#define DPRINTF(x)
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
amigaos_handle_type_attribute (tree *node, tree name, tree args ATTRIBUTE_UNUSED, int flags ATTRIBUTE_UNUSED, bool *no_add_attrs)
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
		  error ("%'stackext%' and %'interrupt%' are mutually exclusive");
		  break;
		}
	    }
	  else if (is_attribute_p ("saveds", name))
	    {
	      if (flag_pic < 3)
		{
		  warning (OPT_Wattributes, "%'%s%' attribute is only usable with fbaserel", IDENTIFIER_POINTER(name));
		}
	      else
	      if (flag_resident)
		{
		  error ("%'saveds%' cannot be used with resident");
		}
	    }
	  else if (is_attribute_p ("entrypoint", name))
	    {
	      if (lookup_attribute ("saveallregs", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("%'entrypoint%' and %'saveallregs%' are mutually exclusive");
		  break;
		}
	    }
	  else if (is_attribute_p ("saveallregs", name))
	    {
	      if (lookup_attribute ("entrypoint", TYPE_ATTRIBUTES(nnn)))
		{
		  error ("%'entrypoint%' and %'saveallregs%' are mutually exclusive");
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
	  if (is_attribute_p ("chip", name) || is_attribute_p ("fast", name) || is_attribute_p ("far", name))
	    {
	      // OK
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
  if (name->base.code != IDENTIFIER_NODE)
	  continue;

  if (is_attribute_p("chip", name) || is_attribute_p("far", name) || is_attribute_p("fast", name))
    {
      if (TREE_TYPE(decl)->base.code == VAR_DECL)
	{
	  error ("%'%s%' attribute can only be specified for variables", IDENTIFIER_POINTER(name));
	  return;
	}

      if (! TREE_STATIC (decl) && ! DECL_EXTERNAL (decl))
	{
	  error ("%'%s%' attribute cannot be specified for local variables", IDENTIFIER_POINTER(name));
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
		  "%'%s%' attribute conflicts with previous declaration", IDENTIFIER_POINTER(name));
	}
    }
  else
    {
//      warning (OPT_Wattributes, "%'%s%' attribute unknown", IDENTIFIER_POINTER(name));
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

  if (0 == strncmp(".data", name, 5) && (!DECL_INITIAL (decl) || initializer_zerop (DECL_INITIAL (decl))))
    {
      extern section * in_section;
      fprintf (asm_out_file, "\t.section .bss%s\n", name + 5);
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


section *
amiga_select_section (tree decl, int reloc ATTRIBUTE_UNUSED,
		    unsigned HOST_WIDE_INT align ATTRIBUTE_UNUSED)
{
  if (decl->base.code == VAR_DECL)
    {
      if (decl->base.constant_flag || decl->base.readonly_flag)
      	return text_section;

      char const * secname = DECL_SECTION_NAME(decl);
      if (secname == 0)
	{
	  tree type = decl->decl_minimal.common.typed.type;
	  if (type->base.code == ARRAY_TYPE)
	    type = type->typed.type;
	  if (type->base.readonly_flag)
	    return text_section;

	  return data_section;
	}
    }

  return default_select_section (decl, reloc, align);
}
