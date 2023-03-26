/* Configuration for GNU C-compiler for m68k Amiga, running AmigaOS.
 *
 * This file is only included and used inside m68k.c to define the target.
 *
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

/* Compile with stack extension.  */
#define MASK_STACKEXTEND 0x40000000 /* 1 << 30 */
#define TARGET_STACKEXTEND (((target_flags & MASK_STACKEXTEND)		\
  && !lookup_attribute ("interrupt",					\
			TYPE_ATTRIBUTES (TREE_TYPE (current_function_decl)))) \
  || lookup_attribute ("stackext",					\
		       TYPE_ATTRIBUTES (TREE_TYPE (current_function_decl))))

///* Compile with stack checking.  */
//
#define MASK_STACKCHECK 0x20000000 /* 1 << 29 */
#define TARGET_STACKCHECK ((target_flags & MASK_STACKCHECK)		\
  && !(target_flags & MASK_STACKEXTEND)					\
  && !lookup_attribute ("interrupt",					\
			TYPE_ATTRIBUTES (TREE_TYPE (current_function_decl))) \
  && !lookup_attribute ("stackext",					\
			TYPE_ATTRIBUTES (TREE_TYPE (current_function_decl))))


/* Provide a dummy entry for the '-msmall-code' switch.  This is used by
   the assembler and '*_SPEC'.  */

#undef SUBTARGET_SWITCHES
#define SUBTARGET_SWITCHES						\
    { "small-code", 0,							\
      "" /* Undocumented. */ },						\
    { "stackcheck", MASK_STACKCHECK,					\
      N_("Generate stack-check code") },				\
    { "no-stackcheck", - MASK_STACKCHECK,				\
      N_("Do not generate stack-check code") },				\
    { "stackextend", MASK_STACKEXTEND,					\
      N_("Generate stack-extension code") },				\
    { "no-stackextend", - MASK_STACKEXTEND,				\
      N_("Do not generate stack-extension code") },			\
    { "fixedstack", - (MASK_STACKCHECK|MASK_STACKEXTEND),		\
      N_("Do not generate stack-check/stack-extension code") },		\
    { "restore-a4", MASK_RESTORE_A4,					\
      N_("Restore a4 in public functions") },				\
    { "no-restore-a4", - MASK_RESTORE_A4,				\
      N_("Do not restore a4 in public functions") },			\
    { "always-restore-a4", MASK_ALWAYS_RESTORE_A4,			\
      N_("Restore a4 in all functions") },				\
    { "no-always-restore-a4", - MASK_ALWAYS_RESTORE_A4,			\
      N_("Do not restore a4 in all functions") }


/* Support sections in chip, fast memory, currently '.datachip', '.datafast'
 * and '.datafar' to abs addressing with baserel.  */
extern void
amiga_named_section (const char *name, unsigned int flags, tree decl);

#undef TARGET_ASM_NAMED_SECTION
#define TARGET_ASM_NAMED_SECTION amiga_named_section

extern section *
amiga_select_section (tree decl, int reloc ATTRIBUTE_UNUSED,
		    unsigned HOST_WIDE_INT align ATTRIBUTE_UNUSED);

#undef  TARGET_ASM_SELECT_SECTION
#define TARGET_ASM_SELECT_SECTION	amiga_select_section


/* Various ABI issues.  */

/* Allow folding division by zero.  */

#define REAL_INFINITY

/* Don't try using XFmode since we don't have appropriate runtime software
   support.  */
#undef LONG_DOUBLE_TYPE_SIZE
#define LONG_DOUBLE_TYPE_SIZE 64

/* We use A4 for the PIC pointer, not A5, which is the framepointer.  */

#undef PIC_OFFSET_TABLE_REGNUM
#define PIC_OFFSET_TABLE_REGNUM (flag_pic ? 12 : INVALID_REGNUM)
 
/* Use A5 as framepointer instead of A6, since the AmigaOS ABI requires A6
   to be used as a shared library base pointer in direct library calls.  */

#undef FRAME_POINTER_REGNUM
#define FRAME_POINTER_REGNUM 13

#undef M68K_REGNAME
#define M68K_REGNAME(r) (reg_names[(r)])

/* The AmigaOS ABI does not define how structures should be returned, so,
   contrary to 'm68k.h', we prefer a multithread-safe solution.  */

#undef PCC_STATIC_STRUCT_RETURN

/* Setup a default shell return value for those (gazillion..) programs that
   (inspite of ANSI-C) declare main() to be void (or even VOID...) and thus
   cause the shell to randomly caugh upon executing such programs (contrary
   to Unix, AmigaOS scripts are terminated with an error if a program returns
   with an error code above the 'error' or even 'failure' level
   (which is configurable with the FAILAT command)).  */

//+2004-06-24  Ulrich Weigand  <uweigand@de.ibm.com>
//+
//+	* c-decl.c (finish_function): Do not check for DEFAULT_MAIN_RETURN.
//+	* system.h (DEFAULT_MAIN_RETURN): Poison.
//+	* doc/tm.texi (DEFAULT_MAIN_RETURN): Remove documentation.
//+

//poison VAR
//#define DEFAULT_MAIN_RETURN c_expand_return (integer_zero_node)

#undef WCHAR_TYPE
#define WCHAR_TYPE "unsigned int"

/* This is how to output an assembler line that says to advance the
   location counter to a multiple of 2**LOG bytes.  */

#ifndef ALIGN_ASM_OP
#define ALIGN_ASM_OP "\t.align\t"
#endif

/* GAS supports alignment up to 32768 bytes.  */
#undef ASM_OUTPUT_ALIGN
#define ASM_OUTPUT_ALIGN(FILE, LOG)					\
do									\
  {									\
    if ((LOG) == 1)							\
      fprintf ((FILE), "\t.even\n");					\
    else								\
      fprintf ((FILE), "\t.align %d\n", (LOG));				\
  }									\
while (0)


/* begin-GG-local: explicit register specification for parameters */

/* Note: this is an extension of m68k_args */


#undef CLASS_MAX_NREGS
#define CLASS_MAX_NREGS(CLASS, MODE)	\
 ((CLASS) == FP_REGS ? GET_MODE_NUNITS (MODE) \
 : ((GET_MODE_SIZE (MODE) + UNITS_PER_WORD - 1) / UNITS_PER_WORD))


/* end-GG-local */

#undef SUBTARGET_OVERRIDE_OPTIONS
#define SUBTARGET_OVERRIDE_OPTIONS					\
do									\
  {									\
    if (flag_resident)							\
      {									\
        if (flag_pic)							\
	  error ("%'-fbaserel%' and %'-resident%' are mutual exclusiv");	\
        flag_pic = flag_resident;					\
      }									\
    if (!TARGET_68020 && flag_pic==4)					\
      error ("%'-fbaserel32%' is not supported on the 68000 or 68010");	\
  }									\
while (0)

/* { name, min_len, max_len, decl_req, type_req, fn_type_req, affects_type_identity, handler, exclude
     } */
#define SUBTARGET_ATTRIBUTES                                            \
  { "chip", 0, 0, false, true, false, false, amigaos_handle_type_attribute, NULL }, \
  { "fast", 0, 0, false, true, false, false, amigaos_handle_type_attribute, NULL }, \
  { "far",  0, 0, false, true, false, false, amigaos_handle_type_attribute, NULL }, \
  { "saveds", 0, 0, false, true, true, false, amigaos_handle_type_attribute, NULL }, \
  { "entrypoint", 0, 0, false, true, true, false, amigaos_handle_type_attribute, NULL }, \
  { "saveallregs", 0, 0, false, true, true, false, amigaos_handle_type_attribute, NULL },

#define GOT_SYMBOL_NAME ""


#define HAVE_ALTERNATE_FRAME_SETUP_F(FSIZE) TARGET_STACKEXTEND

#define ALTERNATE_FRAME_SETUP_F(FSIZE)				\
  (amigaos_alternate_frame_setup_f ((FSIZE)))

#define HAVE_ALTERNATE_FRAME_SETUP(FSIZE) TARGET_STACKEXTEND

#define ALTERNATE_FRAME_SETUP(FSIZE)				\
  (amigaos_alternate_frame_setup ((FSIZE)))

#undef TARGET_INSERT_ATTRIBUTES
#define TARGET_INSERT_ATTRIBUTES amigaos_insert_attribute

