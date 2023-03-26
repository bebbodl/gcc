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

#undef TARGET_AMIGAOS
#define TARGET_AMIGAOS 1

void
amigaos_insert_attribute (tree decl, tree * attr);

extern tree
amigaos_handle_type_attribute (tree *node, tree name, tree args, int flags ATTRIBUTE_UNUSED, bool *no_add_attrs);

extern bool
amigaos_legitimate_src (rtx src);

extern void
amigaos_restore_a4 (void);

extern void
amigaos_alternate_frame_setup_f (int fsize);

extern void
amigaos_alternate_frame_setup (int fsize);
