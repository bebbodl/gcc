/*-
 * Copyright (c) 1991 The Regents of the University of California.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#pragma GCC push_options
#pragma GCC optimize ("-O2")

#include <unistd.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/fcntl.h>

#include "gmon.h"

#include "stabs.h"

#include <exec/memory.h>
#include <exec/interrupts.h>
#include <dos/dos.h>
#include <hardware/custom.h>
#include <hardware/intbits.h>
#include <proto/exec.h>
#include <stdio.h>

void _monstartup(void);
void _moncleanup(void);
__saveallregs void mcount(void);
int profil(char *buf, size_t bufsiz,
                  size_t offset, unsigned int scale);

struct profile_data {
  unsigned short *data;
  size_t count;
  size_t offset;
};
int VertBServer(struct profile_data * p __asm("a1"));


extern const char const _stext;
extern const char const _etext;

#if 0
asm ("
	.globl	mcount
mcount:	movel	a1,-(sp)	| Save A1 as it might be used to store the
	bsr	__mcount	| address of a structure
	movel	(sp)+,a1
	rts
");
#endif

void moncontrol(int mode);

static unsigned int	*store_last_pc;
static unsigned int	dummy;
    /*
     *	froms is actually a bunch of unsigned shorts indexing tos
     */
static int		profiling = 3;
static unsigned short	*froms;
static struct tostruct	*tos = 0;
static long		tolimit = 0;
static char		*s_lowpc = 0;
static char		*s_highpc = 0;
static unsigned long	s_textsize = 0;

static int	ssiz;
static char	*sbuf;
static int	s_scale;
    /* see profil(2) where this is describe (incorrectly) */
#define		SCALE_1_TO_1	0x10000L

#define	MSG "No space for profiling buffer(s)\n"

static inline void *
alloc(int s)
{
  void *res = malloc (s);
  if (res)
    bzero (res, s);
  return res;
}

void _monstartup(void)
{
    int			monsize;
    char		*buffer;
    register int	o;

    char *lowpc;
    char *highpc;

	/*
	 *	round lowpc and highpc to multiples of the density we're using
	 *	so the rest of the scaling (here and in gprof) stays in ints.
	 */
    lowpc = (char *)
	    ROUNDDOWN((unsigned)&_stext, HISTFRACTION*sizeof(HISTCOUNTER));
    s_lowpc = lowpc;
    highpc = (char *)
	    ROUNDUP((unsigned)&_etext, HISTFRACTION*sizeof(HISTCOUNTER));
    s_highpc = highpc;
    s_textsize = highpc - lowpc;
    monsize = (s_textsize / HISTFRACTION)*sizeof(short) + sizeof(struct phdr);
    buffer = alloc( monsize );
    if ( buffer == 0 ) {
	write( 2 , MSG , sizeof(MSG) );
	return;
    }
    froms = (unsigned short *) alloc ( s_textsize / HASHFRACTION );
    if ( froms == 0 ) {
	write( 2 , MSG , sizeof(MSG) );
	froms = 0;
	return;
    }
    tolimit = s_textsize * ARCDENSITY / 100;
    if ( tolimit < MINARCS ) {
	tolimit = MINARCS;
    } else if ( tolimit > 65534 ) {
	tolimit = 65534;
    }
    tos = (struct tostruct *) alloc( tolimit * sizeof( struct tostruct ) );
    if ( tos == 0 ) {
	write( 2 , MSG , sizeof(MSG) );
	froms = 0;
	tos = 0;
	return;
    }
    tos[0].link = 0;
    sbuf = buffer;
    ssiz = monsize;
    ( (struct phdr *) buffer ) -> lpc = (void *)(lowpc - (&_stext - 0)); // was - 4 - why?
    ( (struct phdr *) buffer ) -> hpc = (void *)(highpc - (&_stext - 0));// was - 4 - why?
    ( (struct phdr *) buffer ) -> ncnt = ssiz;
    monsize -= sizeof(struct phdr);
    if ( monsize <= 0 )
	return;
    o = highpc - lowpc;
    if( monsize < o )
    {
	int quot = o / monsize;

	if (quot >= 0x10000)
		s_scale = 1;
	else if (quot >= 0x100)
		s_scale = 0x10000 / quot;
	else if (o >= 0x800000)
		s_scale = 0x1000000 / (o / (monsize >> 8));
	else
		s_scale = 0x1000000 / ((o << 8) / monsize);
    }
    else
	s_scale = SCALE_1_TO_1;
    moncontrol(1);
}

void _moncleanup(void)
{
    FILE *		f;
    int			fromindex;
    int			endfrom;
    char		*frompc;
    int			toindex;
    struct rawarc	rawarc;

    moncontrol(0);
    f = fopen( "gmon.out" , "w");
    if ( !f) {
	perror( "mcount: gmon.out" );
	return;
    }
#ifdef DEBUG_VERSION
	fprintf( stderr , "[mcleanup] sbuf 0x%x ssiz %d\n" , sbuf , ssiz );
#endif
    fwrite(sbuf , ssiz, 1 , f);
    endfrom = s_textsize / (HASHFRACTION * sizeof(*froms));
    for ( fromindex = 0 ; fromindex < endfrom ; fromindex++ ) {
	if ( froms[fromindex] == 0 ) {
	    continue;
	}
	frompc = (void *)(s_lowpc + (fromindex * HASHFRACTION * sizeof(*froms)) - (&_stext - 0));
	for (toindex=froms[fromindex]; toindex!=0; toindex=tos[toindex].link) {
#ifdef DEBUG_VERSION
		fprintf( stderr ,
			"[mcleanup] frompc 0x%x selfpc 0x%x count %d\n" ,
			frompc , tos[toindex].selfpc , tos[toindex].count );
#endif
	    rawarc.raw_frompc = (unsigned long) frompc;
	    rawarc.raw_selfpc = (unsigned long) tos[toindex].selfpc;
	    rawarc.raw_count = tos[toindex].count;
	    fwrite(&rawarc , sizeof rawarc, 1, f);
	}
    }
    fclose( f );
}

__saveallregs void mcount(void)
{
	register char			*selfpc;
	register unsigned short		*frompcindex;
	register struct tostruct	*top;
	register struct tostruct	*prevtop;
	register long			toindex;

	/*
	 *	find the return address for mcount,
	 *	and the return address for mcount's caller.
	 */

	/* selfpc = pc pushed by mcount call.
	   This identifies the function that was just entered.  */
	selfpc = (char *) __builtin_return_address (0);
	/* frompcindex = pc in preceding frame.
	   This identifies the caller of the function just entered.  */
	frompcindex = (void *) __builtin_return_address (1);
	/*
	 *	check that we are profiling
	 *	and that we aren't recursively invoked.
	 */
	if (profiling) {
		goto out;
	}
	profiling++;
	*store_last_pc = (unsigned)selfpc;
	selfpc = selfpc - (int)(&_stext - 0);
	/*
	 *	check that frompcindex is a reasonable pc value.
	 *	for example:	signal catchers get called from the stack,
	 *			not from text space.  too bad.
	 */
#ifdef DEBUG_VERSION
		fprintf (stderr, "from $%x, self $%x (low = $%x)\n",
			 frompcindex, selfpc, s_lowpc);
#endif
	frompcindex = (unsigned short *)((long)frompcindex - (long)s_lowpc);
	if ((unsigned long)frompcindex > s_textsize) {

		goto done;
	}
	frompcindex =
	    &froms[((long)frompcindex) / (HASHFRACTION * sizeof(*froms))];
	toindex = *frompcindex;
#ifdef DEBUG_VERSION
		fprintf (stderr, "frompcindex $%x, froms $%x, toindex = $%x\n",
			 frompcindex, froms, toindex);
#endif
	if (toindex == 0) {
		/*
		 *	first time traversing this arc
		 */
		toindex = ++tos[0].link;
		if (toindex >= tolimit) {
			goto overflow;
		}
		*frompcindex = toindex;
		top = &tos[toindex];
		top->selfpc = selfpc;
		top->count = 1;
		top->link = 0;
		goto done;
	}
	top = &tos[toindex];
	if (top->selfpc == selfpc) {
		/*
		 *	arc at front of chain; usual case.
		 */
		top->count++;
		goto done;
	}
	/*
	 *	have to go looking down chain for it.
	 *	top points to what we are looking at,
	 *	prevtop points to previous top.
	 *	we know it is not at the head of the chain.
	 */
	for (; /* goto done */; ) {
		if (top->link == 0) {
			/*
			 *	top is end of the chain and none of the chain
			 *	had top->selfpc == selfpc.
			 *	so we allocate a new tostruct
			 *	and link it to the head of the chain.
			 */
			toindex = ++tos[0].link;
			if (toindex >= tolimit) {
				goto overflow;
			}
			top = &tos[toindex];
			top->selfpc = selfpc;
			top->count = 1;
			top->link = *frompcindex;
			*frompcindex = toindex;
			goto done;
		}
		/*
		 *	otherwise, check the next arc on the chain.
		 */
		prevtop = top;
		top = &tos[top->link];
		if (top->selfpc == selfpc) {
			/*
			 *	there it is.
			 *	increment its count
			 *	move it to the head of the chain.
			 */
			top->count++;
			toindex = prevtop->link;
			prevtop->link = top->link;
			top->link = *frompcindex;
			*frompcindex = toindex;
			goto done;
		}

	}
done:
	profiling--;
	/* and fall through */
out:
	return;		/* normal return restores saved registers */

overflow:
	profiling++; /* halt further profiling */
#   define	TOLIMIT	"mcount: tos overflow\n"
	write(2, TOLIMIT, sizeof(TOLIMIT));
	goto out;
}



/*
 * Control profiling
 *	profiling is what mcount checks to see if
 *	all the data structures are ready.
 */
void moncontrol(int mode)
{
    if (mode) {
	/* start */
	store_last_pc = (unsigned *)profil(sbuf + sizeof(struct phdr),
			       ssiz - sizeof(struct phdr), (int)s_lowpc, s_scale);
        if (store_last_pc == NULL)
            store_last_pc = &dummy;
	profiling = 0;
    } else {
	/* stop */
	profil((char *)0, 0, 0, 0);
	profiling = 3;
    }
}

ADD2INIT(_monstartup,-4);
ADD2EXIT(_moncleanup,-4);

struct profile_data vbdata;

struct Interrupt vbint;

int VertBServer(struct profile_data * p __asm("a1")) {
  asm("move.l a0,-(sp)");
  register char * usp __asm("a0");
  asm("move.l sp,a0");

  size_t index = (*((size_t *)(usp + 0x32)) - p->offset) >> 1;
  if (index < p->count)
    ++p->data[index];
  asm("move.l (sp)+,a0");
  return 0;
}

int profil(char *buf, size_t bufsiz,
                  size_t offset, unsigned int scale) {
  if (buf) {
      // install interrupt if not running
      if (vbdata.data)
	return -1;

      vbdata.data = (unsigned short *)buf;
      vbdata.count = bufsiz>>1;
      vbdata.offset = offset;

      vbint.is_Node.ln_Type = NT_INTERRUPT;         /* Initialize the node. */
      vbint.is_Node.ln_Pri = 20;
      vbint.is_Node.ln_Name = "gcc profiler";
      vbint.is_Data = (APTR)&vbdata;
      vbint.is_Code = VertBServer;

      AddIntServer(INTB_VERTB, &vbint); /* Kick this interrupt server to life. */

      return 0;
  }

  if (!vbdata.data)
    return -1;

  vbdata.count = 0;
  RemIntServer(INTB_VERTB, &vbint);
  vbdata.data = 0;
  return 0;
}

#pragma GCC pop_options
