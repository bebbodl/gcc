/* Relative (relocatable) prefix support.
   Copyright (C) 1987, 1989, 1992, 1993, 1994, 1995, 1996, 1997, 1998,
   1999, 2000, 2001, 2002, 2006, 2012 Free Software Foundation, Inc.

This file is part of libiberty.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 2, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING.  If not, write to the Free
Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
02110-1301, USA.  */

/*

@deftypefn Extension {const char*} make_relative_prefix (const char *@var{progname}, @
  const char *@var{bin_prefix}, const char *@var{prefix})

Given three paths @var{progname}, @var{bin_prefix}, @var{prefix},
return the path that is in the same position relative to
@var{progname}'s directory as @var{prefix} is relative to
@var{bin_prefix}.  That is, a string starting with the directory
portion of @var{progname}, followed by a relative pathname of the
difference between @var{bin_prefix} and @var{prefix}.

If @var{progname} does not contain any directory separators,
@code{make_relative_prefix} will search @env{PATH} to find a program
named @var{progname}.  Also, if @var{progname} is a symbolic link,
the symbolic link will be resolved.

For example, if @var{bin_prefix} is @code{/alpha/beta/gamma/gcc/delta},
@var{prefix} is @code{/alpha/beta/gamma/omega/}, and @var{progname} is
@code{/red/green/blue/gcc}, then this function will return
@code{/red/green/blue/../../omega/}.

The return value is normally allocated via @code{malloc}.  If no
relative prefix can be found, return @code{NULL}.

@end deftypefn

*/

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#ifdef HAVE_SYS_STAT_H
#include <sys/stat.h>
#endif
#include <sys/types.h>
#include <dirent.h>
#include <string.h>

#include "ansidecl.h"
#include "libiberty.h"

/* This is for the FreeBSD specific bits to get current program path */
#if defined(__FreeBSD__)
#include <sys/sysctl.h>
#include <err.h>
#endif

#ifndef R_OK
#define R_OK 4
#define W_OK 2
#define X_OK 1
#endif

#ifndef DIR_SEPARATOR
#  define DIR_SEPARATOR '/'
#endif

#if defined (_WIN32) || defined (__MSDOS__) \
    || defined (__DJGPP__) || defined (__OS2__)
#  define HAVE_DOS_BASED_FILE_SYSTEM
#  define HAVE_HOST_EXECUTABLE_SUFFIX
#  define HOST_EXECUTABLE_SUFFIX ".exe"
#  ifndef DIR_SEPARATOR_2 
#    define DIR_SEPARATOR_2 '\\'
#  endif
#  define PATH_SEPARATOR ';'
#else
#  define PATH_SEPARATOR ':'
#endif

#ifndef DIR_SEPARATOR_2
#  define IS_DIR_SEPARATOR(ch) ((ch) == DIR_SEPARATOR)
#else
#  define IS_DIR_SEPARATOR(ch) \
	(((ch) == DIR_SEPARATOR) || ((ch) == DIR_SEPARATOR_2))
#endif

#define DIR_UP ".."

static char *save_string (const char *, int);
static char **split_directories	(const char *, int *);
static void free_split_directories (char **);

static char *
save_string (const char *s, int len)
{
  char *result = (char *) malloc (len + 1);

  memcpy (result, s, len);
  result[len] = 0;
  return result;
}

/* Split a filename into component directories.  */

static char **
split_directories (const char *name, int *ptr_num_dirs)
{
  int num_dirs = 0;
  char **dirs;
  const char *p, *q;
  int ch;

  /* Count the number of directories.  Special case MSDOS disk names as part
     of the initial directory.  */
  p = name;
#ifdef HAVE_DOS_BASED_FILE_SYSTEM
  if (name[1] == ':' && IS_DIR_SEPARATOR (name[2]))
    {
      p += 3;
      num_dirs++;
    }
#endif /* HAVE_DOS_BASED_FILE_SYSTEM */

  while ((ch = *p++) != '\0')
    {
      if (IS_DIR_SEPARATOR (ch))
	{
	  num_dirs++;
	  while (IS_DIR_SEPARATOR (*p))
	    p++;
	}
    }

  dirs = (char **) malloc (sizeof (char *) * (num_dirs + 2));
  if (dirs == NULL)
    return NULL;

  /* Now copy the directory parts.  */
  num_dirs = 0;
  p = name;
#ifdef HAVE_DOS_BASED_FILE_SYSTEM
  if (name[1] == ':' && IS_DIR_SEPARATOR (name[2]))
    {
      dirs[num_dirs++] = save_string (p, 3);
      if (dirs[num_dirs - 1] == NULL)
	{
	  free (dirs);
	  return NULL;
	}
      p += 3;
    }
#endif /* HAVE_DOS_BASED_FILE_SYSTEM */

  q = p;
  while ((ch = *p++) != '\0')
    {
      if (IS_DIR_SEPARATOR (ch))
	{
	  while (IS_DIR_SEPARATOR (*p))
	    p++;

	  dirs[num_dirs++] = save_string (q, p - q);
	  if (dirs[num_dirs - 1] == NULL)
	    {
	      dirs[num_dirs] = NULL;
	      free_split_directories (dirs);
	      return NULL;
	    }
	  q = p;
	}
    }

  if (p - 1 - q > 0)
    dirs[num_dirs++] = save_string (q, p - 1 - q);
  dirs[num_dirs] = NULL;

  if (dirs[num_dirs - 1] == NULL)
    {
      free_split_directories (dirs);
      return NULL;
    }

  if (ptr_num_dirs)
    *ptr_num_dirs = num_dirs;
  return dirs;
}

/* Release storage held by split directories.  */

static void
free_split_directories (char **dirs)
{
  int i = 0;

  if (dirs != NULL)
    {
      while (dirs[i] != NULL)
	free (dirs[i++]);

      free ((char *) dirs);
    }
}


#if defined(__FreeBSD__)
static size_t
bsd_get_current_executable_path(char *buf, size_t len)
{
  size_t llen;
  int ret;
  int mib[4];

  mib[0] = CTL_KERN;
  mib[1] = KERN_PROC;
  mib[2] = KERN_PROC_PATHNAME;
  mib[3] = -1;

  llen = len;
  ret = sysctl(mib, 4, buf, &llen, NULL, 0);
  if (ret != 0) {
    warn("%s: sysctl for exec path", __func__);
    return 0;
  }
  return llen;
}


#endif /* __FreeBSD__ */

/* Given three strings PROGNAME, BIN_PREFIX, PREFIX, return a string that gets
   to PREFIX starting with the directory portion of PROGNAME and a relative
   pathname of the difference between BIN_PREFIX and PREFIX.

   For example, if BIN_PREFIX is /alpha/beta/gamma/gcc/delta, PREFIX is
   /alpha/beta/gamma/omega/, and PROGNAME is /red/green/blue/gcc, then this
   function will return /red/green/blue/../../omega/.

   If no relative prefix can be found, return NULL.  */

static char *
make_relative_prefix_1 (const char *progname, const char *bin_prefix,
			const char *prefix, const int resolve_links)
{
  char **prog_dirs = NULL, **bin_dirs = NULL, **prefix_dirs = NULL;
  int prog_num, bin_num, prefix_num;
  int i, n, common;
  int needed_len;
  char *ret = NULL, *ptr, *full_progname;
  char buf[1024], *p, *q, *t;
  DIR * d;

  if (progname == NULL || bin_prefix == NULL || prefix == NULL)
    return NULL;

#ifdef __amiga__
//printf("prog=<%s> bin_prefix=<%s> prefix=<%s>\t", progname, bin_prefix, prefix);
#endif

  buf[0] = 0;
#if defined(__amiga__)
  strcpy(buf, "GCC:");
  n = strlen("GCC:");
#elif defined(__MSYS__)
  n = GetModuleFileNameA(0, buf, 1023);
#elif defined(__MACH__)
  n = 1022;
  n |= _NSGetExecutablePath(buf, &n);
#elif defined(__sun) && defined(__SVR4)
  n = readlink( "/proc/self/path/a.out", buf, 1023);
#elif defined(__FreeBSD__)
  n = bsd_get_current_executable_path(buf, 1023);
#else
  n = readlink( "/proc/self/exe", buf, 1023);
#endif
  if (n < 0 || n > 1022)
    return NULL;
  else if (n)
    buf[n] = 0;

  //puts(buf);
#if !defined(__amiga__)
  buf[1023] = 0;
  for (p = buf; *p; ++p)
    if (*p == '\\')
      *p = '/';

  // remove program and bin folder
  i = 2;
  while (p > buf) {
      if (*--p == '/') {
	  *p = 0;
	  if (--i == 0)
	    break;
      }
  }
#endif
  // find common path in bin_prefix and prefix
  for (p = bin_prefix, q = prefix; *p && *p == *q; ++p, ++q)
    {}

#if defined(__amiga__)
  p = concat(buf, q, NULL);
#else
  p = concat(buf, "/", q, NULL);
#endif

  // normalize
  while ((t = strstr(p, "/../")))
    {
      char * r = t - 1;
      while (r >= p && *r != '/')
	--r;
      if (r < p)
	break;
      memmove(r, t + 3, strlen(t + 3) + 1);
    }


#ifdef __amiga__
//  printf("try:\t<%s>\n", p);
  // remove trailing /
  char * s = p + strlen(p);
  while (s > p && *--s == '/')
    *s = 0;
#endif

  d = opendir(p);
#ifdef __amiga__
  if (*s != ':')
    {
      *++s = '/';
      *++s = 0;
    }
#endif
  if (d) closedir(d);
  else
    {
// printf("can't open dir: %s\n", p);
      free(p);
      strcpy(buf, prefix);
      buf[q - prefix] = 0;
      p = concat(buf, q, NULL);
    }
  
#ifdef __amiga__
//  printf("->\t<%s>\n", p);
#endif

  return p;
}


/* Do the full job, including symlink resolution.
   This path will find files installed in the same place as the
   program even when a soft link has been made to the program
   from somwhere else. */

char *
make_relative_prefix (const char *progname, const char *bin_prefix,
		      const char *prefix)
{
  return make_relative_prefix_1 (progname, bin_prefix, prefix, 1);
}

/* Make the relative pathname without attempting to resolve any links.
   '..' etc may also be left in the pathname.
   This will find the files the user meant the program to find if the
   installation is patched together with soft links. */

char *
make_relative_prefix_ignore_links (const char *progname,
				   const char *bin_prefix,
				   const char *prefix)
{
  return make_relative_prefix_1 (progname, bin_prefix, prefix, 0);
}

