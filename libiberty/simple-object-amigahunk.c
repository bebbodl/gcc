/* simple-object-amigahunk.c -- routines to manipulate Amiga hunk object files.
 Copyright 2010 Free Software Foundation, Inc.
 Written by Stefan "Bebbo" Franke @ Bebbosoft GbR.

 This program is free software; you can redistribute it and/or modify it
 under the terms of the GNU General Public License as published by the
 Free Software Foundation; either version 2, or (at your option) any
 later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, 51 Franklin Street - Fifth Floor,
 Boston, MA 02110-1301, USA.  */

#include "config.h"
#include "libiberty.h"
#include "simple-object.h"

#include <errno.h>
#include <stddef.h>

#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif

#ifdef HAVE_STDIO_H
#include <stdio.h>
#endif

#ifdef HAVE_STDINT_H
#include <stdint.h>
#endif

#ifdef HAVE_STRING_H
#include <string.h>
#endif

#ifdef HAVE_INTTYPES_H
#include <inttypes.h>
#endif

#include "simple-object-common.h"

/**
 * all info needed to find hunks aka sections.
 */
struct hunk
{
  struct hunk * next;
  char const * name;
  off_t offset;
  unsigned length;
};

/**
 * Used during initial file read.
 * Track the hunks plus the name.
 */
struct simple_object_amigahunk_read
{
  struct hunk * root;
  char const * name;
  int deleted;
};

/**
 * A copy of simple_object_amigahunk_read atm.
 * /
struct simple_object_amigahunk_attributes
{
  struct hunk * root;
  char const * name;
};
*/
#define simple_object_amigahunk_attributes simple_object_amigahunk_read

/**
 * Read 4 bytes as big endian int and move the file offset.
 */
static unsigned
read4 (int descriptor, off_t * offset)
{
  static unsigned char b[4];
  const char *errmsg;
  int err;

  if (!simple_object_internal_read (descriptor, *offset, b, 4, &errmsg, &err))
    return 0xffffffff;
  *offset += 4;
  return (b[0] << 24) | (b[1] << 16) | (b[2] << 8) | b[3];
}

// not reentrant atm.
static unsigned nameLen; // size of current name
static unsigned char * name;    // some name

/**
 * Read a name into the shared buffer.
 */
static int
readName (unsigned l, int descriptor, off_t * offset)
{
  const char *errmsg;
  int err;
  l <<= 2;
  if (nameLen < l)
    {
      XDELETE(name);
      name = XNEWVEC(unsigned char, l + 1);
      nameLen = l;
    }
  if (!l)
    {
      if (!name)
	name = XNEWVEC(unsigned char, 1);
      *name = 0;
      return 1;
    }
  int r = simple_object_internal_read (descriptor, *offset, name, l, &errmsg,
				       &err);
  name[l] = 0;
  if (r)
    *offset += l;
  return r;
}

/* See if we have an Amiga file.
 * Also remember all hunks.
 */

static void *
simple_object_amigahunk_match (
    unsigned char header[SIMPLE_OBJECT_MATCH_HEADER_LEN], int descriptor,
    off_t offset, const char *segment_name ATTRIBUTE_UNUSED,
    const char **errmsg, int *err)
{
  if (header[0] != 0 || header[1] != 0 || header[2] != 3 || header[3] != 0xe7)
    return NULL;

//  fprintf (stderr, "simple_object_amigahunk_match\n");

  struct simple_object_amigahunk_read * oar = XNEW(
      struct simple_object_amigahunk_read);
  oar->root = NULL;
  oar->name = NULL;
  oar->deleted = 0;

  for (;;)
    {
      unsigned hid = read4 (descriptor, &offset);
      if (hid == 0xffffffff)
	break;
      if (hid == 0x3f2)
	continue;

      unsigned sz = read4 (descriptor, &offset);
      switch (hid & 0x3fffffff)
	{
	case 0x3f3: // HEADER
	  if (sz)
	    {
	      readName (sz, descriptor, &offset);
	    }
	  // first last + sizes
	  unsigned nsecs = read4 (descriptor, &offset);
	  unsigned first = read4 (descriptor, &offset);
	  unsigned last = read4 (descriptor, &offset);
	  unsigned i;
	  for (i = 0; i < nsecs; ++i)
	    {
	      sz = read4 (descriptor, &offset);
	    }
	  break;

	case 0x3e8: // NAME
	  readName (sz, descriptor, &offset);

	  struct hunk * h = XNEW(struct hunk);
	  h->next = oar->root;
	  h->name = xstrdup ((char const*) name);

	  offset += 4;
	  h->length = read4 (descriptor, &offset) * 4;
	  h->offset = offset;
	  offset -= 8;

	  oar->root = h;
	  break;
	case 0x3e7: // UNIT
	  {
	      readName (sz, descriptor, &offset);
	      oar->name = xstrdup ((char const *) name);
	      break;
	  }
	case 0x3e9: // CODE
	case 0x3ea: // DATA
	case 0x3f1: // DEBUG
		    // skip sz long words.
	  offset += sz * 4;
	  break;

	case 0x3eb: // BSS
		    // no more data
	  break;

	case 0x3ec: // RELOC32
	case 0x3ed: // RELOC16
	case 0x3ee: // RELOC8
	case 0x3f7: // DRELOC32
	case 0x3f8: // DRELOC16
	case 0x3f9: // DRELOC8
	case 0x3f0: // SYMBOL
	case 0x3fe: // ABSRELOC16
	  while (sz)
	    {
	      unsigned hn = read4 (descriptor, &offset);
	      offset += sz * 4;
	      sz = read4 (descriptor, &offset);
	    }
	  break;

	case 0x3fc: // RELOC32SHORT
	  while (sz)
	    {
	      unsigned hn = read4 (descriptor, &offset);
	      offset += sz * 2;
	      sz = read4 (descriptor, &offset);
	    }
	  break;

	case 0x3ef: // EXT
	  while (sz & 0xff000000)
	    {
	      unsigned l = sz & 0xffffff;
	      unsigned b = sz >> 24;
	      readName (l, descriptor, &offset);
	      switch (b)
		{
		case 0: // ext_symb
		case 1: // ext_def
		case 2: // ext_abs
		case 3: // ext_res
		  {
		    offset += 4;
		  }
		  break;
		case 130: // ext_common EXT_ABSCOMMON
		case 137: // EXT_RELCOMMON
		case 208: // EXT_DEXT32COMMON
		case 209: // EXT_DEXT16COMMON
		case 210: // EXT_DEXT8COMMON
		  {
		    offset += 4;
		    unsigned blocksize = read4 (descriptor, &offset);
		    offset += blocksize * 4;
		  }
		  break;
		case 129: // ext_ref32
		case 131: // ext_ref16
		case 132: // ext_ref8
		case 133: // ext_dref32
		case 134: // ext_dref16
		case 135: // ext_dref8
		case 136: // EXT_RELREF32
		case 138: // EXT_ABSREF16
		case 139: // EXT_ABSREF8
		  {
		    unsigned n = read4 (descriptor, &offset);
		    offset += n * 4;
		  }
		  break;
		default:
		  break;
		}

	      sz = read4 (descriptor, &offset);
	    }
	  break;
	}
    }

  return (void *) oar;
}

/* Find all sections in an Amiga file.
 * invoke the callback pfn if section name matches.
 */

static const char *
simple_object_amigahunk_find_sections (simple_object_read *sobj, int
(*pfn) (void *, const char *, off_t offset, off_t length),
				       void *data, int *err)
{
  struct simple_object_amigahunk_read *eor =
      (struct simple_object_amigahunk_read *) sobj->data;
  struct hunk * h = eor->root;

//  fprintf (stderr, "simple_object_amigahunk_find_sections\n");

  while (h)
    {
      if (!(*pfn) (data, h->name, h->offset, h->length))
	{
//	  fprintf (stderr, "simple_object_amigahunk_find_sections: %s\n", h->name);
	  break;
	}
      h = h->next;
    }

  return NULL;
}

/* Fetch the attributes for an simple_object_read.  */

static void *
simple_object_amigahunk_fetch_attributes (simple_object_read *sobj,
					  const char **errmsg ATTRIBUTE_UNUSED,
					  int *err ATTRIBUTE_UNUSED)
{
  struct simple_object_amigahunk_read *eor =
      (struct simple_object_amigahunk_read *) sobj->data;
  struct simple_object_amigahunk_attributes *ret;

//  fprintf (stderr, "simple_object_amigahunk_fetch_attributes\n");

  ret = XNEW(struct simple_object_amigahunk_attributes);

  *ret = *eor;
  eor->deleted = 1;

  return ret;
}

/* Release the privata data for an simple_object_read.  */

static void
simple_object_amigahunk_release_read (void *data)
{
  struct simple_object_amigahunk_read *eor =
      (struct simple_object_amigahunk_read *) data;

  if (!eor->deleted)
    {
      struct hunk * h = eor->root;
      while (h)
	{
	  struct hunk * n = h;
	  h = h->next;
	  XDELETE(n);
	}
      XDELETE(eor->name);
    }
  XDELETE(data);
}

/* Compare two attributes structures.
 * Not yet implemented.
 */

static const char *
simple_object_amigahunk_attributes_merge (void *todata, void *fromdata,
					  int *err)
{
  struct simple_object_amigahunk_attributes *to =
      (struct simple_object_amigahunk_attributes *) todata;
  struct simple_object_amigahunk_attributes *from =
      (struct simple_object_amigahunk_attributes *) fromdata;

//  fprintf (stderr, "simple_object_amigahunk_attributes_merge\n");

  return NULL;
}

/* Release the private data for an attributes structure.  */

static void
simple_object_amigahunk_release_attributes (void *data)
{
  simple_object_amigahunk_release_read(data);
}

/* Prepare to write out a file.  */

static void *
simple_object_amigahunk_start_write (void *attributes_data,
				     const char **errmsg ATTRIBUTE_UNUSED,
				     int *err ATTRIBUTE_UNUSED)
{
  struct simple_object_amigahunk_attributes *attrs =
      (struct simple_object_amigahunk_attributes *) attributes_data;
  struct simple_object_amigahunk_attributes *ret;

  /* We're just going to record the attributes, but we need to make a
   copy because the user may delete them.  */
  ret = XNEW(struct simple_object_amigahunk_attributes);

//  fprintf (stderr, "simple_object_amigahunk_start_write\n");

  *ret = *attrs;

  attrs->deleted = 1;

  return ret;
}

/**
 * Write a name in Amiga hunk style.
 */
static int
write_name (int descriptor, off_t * offset, char const * name,
	    const char **errmsg, int *err)
{
  unsigned slen = strlen (name);
  unsigned len = (slen + 3) >> 2;
  unsigned char b[4];
  b[3] = len;
  b[2] = len >> 8;
  b[1] = len >> 16;
  b[0] = 0;

  if (!simple_object_internal_write (descriptor, *offset, b, 4, errmsg, err))
    return 0;

  *offset += 4;

  if (!simple_object_internal_write (descriptor, *offset,
				     (unsigned char const *) name, slen, errmsg,
				     err))
    return 0;

  *offset += slen;

  slen = (len << 2) - slen;
  if (slen)
    {
      b[1] = 0;
      b[2] = 0;
      if (!simple_object_internal_write (descriptor, *offset, b, slen, errmsg,
					 err))
	return 0;

      *offset += slen;
    }

  return 1;
}

/* Write out a complete Amiga file. */

static const char *
simple_object_amigahunk_write_to_file (simple_object_write *sobj,
				       int descriptor, int *err)
{
  struct simple_object_amigahunk_attributes *attrs =
      (struct simple_object_amigahunk_attributes *) sobj->data;
  const char *errmsg;
  simple_object_write_section *section;
  unsigned int shnum;
  off_t offset = 0;
  static const unsigned char HUNK_UNIT[] =
    { 0, 0, 3, 0xe7 };
  static const unsigned char HUNK_NAME[] =
    { 0, 0, 3, 0xe8 };
  static const unsigned char HUNK_DEBUG[] =
    { 0, 0, 3, 0xf1 };
  static const unsigned char HUNK_END[] =
    { 0, 0, 3, 0xf2 };

//  fprintf (stderr, "simple_object_amigahunk_write_to_file\n");

  // write header
  if (!simple_object_internal_write (descriptor, offset, HUNK_UNIT, 4, &errmsg,
				     err))
    return NULL;
  offset += 4;
  if (!write_name (descriptor, &offset, attrs->name, &errmsg, err))
    return NULL;

  shnum = 0;
  for (section = sobj->sections; section != NULL; section = section->next)
    {
//      fprintf (stderr, "%d: %s\n", shnum, section->name);

      if (!simple_object_internal_write (descriptor, offset, HUNK_NAME, 4,
					 &errmsg, err))
	return NULL;
      offset += 4;
      if (!write_name (descriptor, &offset, section->name, &errmsg, err))
	return NULL;

      if (!simple_object_internal_write (descriptor, offset, HUNK_DEBUG, 4,
					 &errmsg, err))
	return NULL;
      offset += 4;

      // collect data len
      struct simple_object_write_section_buffer * sb;
      size_t slen = 0;
      for (sb = section->buffers; sb; sb = sb->next)
	slen += sb->size;

      unsigned len = (slen + 3) >> 2;
      unsigned char b[4];
      b[3] = len;
      b[2] = len >> 8;
      b[1] = len >> 16;
      b[0] = 0;

      if (!simple_object_internal_write (descriptor, offset, b, 4, &errmsg,
					 err))
	return 0;

      offset += 4;

      // write data
      for (sb = section->buffers; sb; sb = sb->next)
	{
	  if (!simple_object_internal_write (descriptor, offset,
					     (unsigned char const *) sb->buffer,
					     sb->size, &errmsg, err))
	    return 0;
	  offset += sb->size;
	}

      // pad
      slen = (len << 2) - slen;
      if (slen)
	{
	  b[1] = 0;
	  b[2] = 0;
	  if (!simple_object_internal_write (descriptor, offset, b, slen,
					     &errmsg, err))
	    return 0;

	  offset += slen;
	}

      if (!simple_object_internal_write (descriptor, offset, HUNK_END, 4, &errmsg,
					 err))
	return NULL;
      offset += 4;

      ++shnum;
    }
  if (shnum == 0)
    return NULL;

  return NULL;
}

/* Release the private data for an simple_object_write structure.  */

static void
simple_object_amigahunk_release_write (void *data)
{
  simple_object_amigahunk_release_read(data);
}

/* The Amiga functions.  */

const struct simple_object_functions simple_object_amigahunk_functions =
  { simple_object_amigahunk_match, simple_object_amigahunk_find_sections,
      simple_object_amigahunk_fetch_attributes,
      simple_object_amigahunk_release_read,
      simple_object_amigahunk_attributes_merge,
      simple_object_amigahunk_release_attributes,
      simple_object_amigahunk_start_write,
      simple_object_amigahunk_write_to_file,
      simple_object_amigahunk_release_write };
