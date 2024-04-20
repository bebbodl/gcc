#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"
#include "insn-modes.h"

bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed);

enum mycosts {
  cost_base,
  cost_reg,
  cost_mem,
  cost_int_moveq,
  cost_int_addq,
  cost_word,
  cost_long,
  cost_float,
  cost_double,
  cost_extended,
  cost_addr_ax,
  cost_addr_nax,
  cost_addr_symbol,
  cost_addr_axdx,
  cost_addr_n8axdx,
  cost_addr_n16axdx,
  cost_addr_n32axdx,
  cost_addr_with_mem,
  cost_shift,
  cost_mult,
  cost_div,
  cost_call,
  cost_if,
  cost_bcc,
  cost_max
};

static int thecosts0[cost_max] = {
    0, // set
    2, // reg
    5, // mem
    2, // int moveq
    2, // int addq
    2, // int word was 1
    2, // int long was 2
    2, // fix/float SF
    4, // double DF
    6, // extended XF
    0, // (ax)
    1, // (n,ax), was 1
    1, // symbol, was 1
    2, // (ax,dy) was 3
    2, // (n8,ax,dy) was 3
    2, // (n16,ax,dy) was 4
    3, // (n32,ax,dy) was 5
    35, // other address
    0, // shift
    8, // mult
    60, // div
    7, // call
    16, // if then else
    16, // bcc
};

static int thecosts2[cost_max] = {
    2, // set
    1, // reg
    4, // mem
    1, // int moveq
    1, // int addq
    1, // int word was 1
    1, // int long was 2
    3, // fix/float SF
    5, // double DF
    7, // extended XF
    0, // (ax)
    0, // (n,ax), was 1
    0, // symbol, was 1
    0, // (ax,dy) was 3
    0, // (n8,ax,dy) was 3
    0, // (n16,ax,dy) was 4
    0, // (n32,ax,dy) was 5
    35, // other address
    0, // shift
    8, // mult
    60, // div
    7, // call
    16, // if then else
    16, // bcc
};

static int thecosts4[cost_max] = {
    4, // set
    0, // reg
    3, // mem
    0, // moveq
    0, // addq
    0, // word was 1
    0, // long was 2
    4, // fix/float SF
    6, // double DF
    8, // extended XF
    0, // (ax)
    0, // (n,ax), was 1
    0, // symbol, was 1
    4, // (ax,dy) was 3
    4, // (n8,ax,dy) was 3
    8, // (n16,ax,dy) was 4
    8, // (n32,ax,dy) was 5
    35, // other address
    0, // shift
    8, // mult
    60, // div
    7, // call
    16, // if then else
    16, // bcc
};

static int * thecosts = thecosts0;

#if 1
static int ttotal;
#define TEST(a,r) {ttotal = 0; m68k_68080_costs(a, SImode, 0, 0, &ttotal, 1); if (ttotal != r) {debug(a);printf("%d <> %d: %s\n", ttotal, r, #a);}}

void
selftest_m68k_68080_costs (void)
{
  rtx d0 = gen_rtx_REG (SImode, 0);
  rtx d1 = gen_rtx_REG (SImode, 1);
  rtx a7 = gen_rtx_REG (SImode, 15);

  rtx c120 = GEN_INT(120);

  rtx mem_120ia0 = gen_rtx_MEM (SImode, gen_rtx_PLUS(SImode, a7, c120));

  rtx dummy = gen_rtx_SYMBOL_REF(SImode, "dummy");
  rtx minusa7 = gen_rtx_MEM(SImode, gen_rtx_PRE_DEC(SImode, a7));

  rtx movel_d0_d1 = gen_rtx_SET(d1, d0);
  TEST(movel_d0_d1, thecosts[cost_base] + thecosts[cost_reg] * 2);

  rtx add_d0_d1 = gen_rtx_SET(d1, gen_rtx_PLUS(SImode, d1, d0));
  TEST(add_d0_d1, thecosts[cost_base] + thecosts[cost_reg] * 2);

  rtx movel_120ia0_d0 = gen_rtx_SET(d0, mem_120ia0);
  TEST(movel_120ia0_d0, thecosts[cost_base] + thecosts[cost_reg]  + thecosts[cost_mem] + thecosts[cost_addr_ax]);

  rtx ashl_8_d0 = gen_rtx_SET(d0, gen_rtx_ASHIFT(SImode, d0, GEN_INT(8)));
  TEST(ashl_8_d0, thecosts[cost_base] + thecosts[cost_reg] + thecosts[cost_int_addq]);

  rtx pea_sym = gen_rtx_SET(minusa7, dummy);
  TEST(pea_sym, thecosts[cost_base] + thecosts[cost_long]  + thecosts[cost_mem] + thecosts[cost_addr_ax]);

  rtx pea_32 = gen_rtx_SET(minusa7, GEN_INT(32));
  TEST(pea_32, thecosts[cost_base] + thecosts[cost_reg]  + thecosts[cost_mem] + thecosts[cost_addr_nax]);

  rtx addq8sp = gen_rtx_SET(a7, gen_rtx_PLUS(SImode, a7, GEN_INT(8)));
  TEST(addq8sp, thecosts[cost_base] + thecosts[cost_reg] * 2);

  rtx cmpd0a7 = gen_rtx_SET(cc0_rtx, gen_rtx_COMPARE(SImode, d0, a7));
  TEST(cmpd0a7, thecosts[cost_base] + thecosts[cost_reg] * 2);
}
static int run;
#endif


/**
 * calculate costs for the 68080.
 * opno == 1: calculate as if dst is a register
 * opno == 0: calculate difference to register assignment
 */
bool
m68k_68080_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed)
{
//  if (!run)
//    {
//      run = 1;
//      selftest_m68k_68080_costs ();
//    }

  int code = GET_CODE(x);
  int total2 = 0;
  *total = 0;

  if (outer_code == ADDRESS)
    {
      if (GET_CODE (x) == CONST)
	x = XEXP(x, 0);
      if (REG_P(x) || GET_CODE(x) == POST_INC || GET_CODE(x) == PRE_DEC)
	{
	  *total = thecosts[cost_addr_ax]; // (ax), (ax)+, -(ax)
	  return true;
	}
      if (GET_CODE(x) == SYMBOL_REF || GET_CODE(x) == LABEL_REF || CONST_INT_P(x))
	{
	  *total = thecosts[cost_addr_symbol];
	  return true;
	}
      if (GET_CODE(x) == MULT)
	{
	  *total = thecosts[cost_addr_axdx];
	  return true;
	}

      if (GET_CODE(x) == PLUS)
	{
	  rtx b = XEXP(x, 0);
	  if (GET_CODE(b) == CONST)
	    b = XEXP(b, 0);
	  rtx c = XEXP(x, 1);
	  if (GET_CODE(c) == CONST)
	    c = XEXP(c, 0);

	  if ((GET_CODE(b) == SYMBOL_REF || GET_CODE(b) == LABEL_REF  || CONST_INT_P(b))
	      && CONST_INT_P(c))
	    {
	      *total = thecosts[cost_addr_symbol]; // sym+n
	      return true;
	    }

	  if (REG_P(b) && GET_CODE(c) == CONST_INT && INTVAL(c) >= -32768
	      && INTVAL(c) <= 37267)
	    {
	      *total = thecosts[cost_addr_nax]; // 16(An),Dn
	      return true;
	    }
	  if (REG_P(b) || GET_CODE(b) == MULT || GET_CODE(b) == ASHIFT)
	    {
	      if (REG_P(c))
		{
		  *total = thecosts[cost_addr_axdx]; // (An,Xn*S)
		  return true;
		}
	      if (REG_P(c) || GET_CODE(c) == SYMBOL_REF
		  || GET_CODE(c) == CONST_INT)
		{
		  *total = thecosts[cost_addr_n32axdx]; // (32,Xn*S)
		  return true;
		}
	    }
	  if (GET_CODE(b) == PLUS)
	    {
	      rtx b0 = XEXP(b, 0);
	      rtx b1 = XEXP(b, 1);
	      if (REG_P(b0) || GET_CODE(b0) == MULT || GET_CODE(b0) == ASHIFT)
		{
		  if (GET_CODE(c) == CONST_INT)
		    {
		      *total = INTVAL(c) >= -8 && INTVAL(c) <= 8 ? thecosts[cost_addr_n8axdx] // 8(An,Xn*S)
			  :
			       INTVAL(c) >= -32768 && INTVAL(c) <= 32767 ? thecosts[cost_addr_n16axdx] // (16,An,Xn*S)
				   : thecosts[cost_addr_n32axdx]; // (32,An,Xn*S)
		      return true;
		    }
		  if (GET_CODE(c) == SYMBOL_REF || GET_CODE(c) == LABEL_REF || CONST_INT_P(c))
		    {
		      *total = thecosts[cost_addr_n32axdx];
		      return true;
		    }
		}
	      if (GET_CODE(b0) == SYMBOL_REF && CONST_INT_P(b1))
		{
		  *total = thecosts[cost_addr_n32axdx];
		  return true;
		}
	    }
	  if (GET_CODE(c) == PLUS)
	    {
	      *total = thecosts[cost_addr_n32axdx];
	      return true;
	    }
	}
      *total = thecosts[cost_addr_ax];
      return true;
    }

  switch (code)
    {
    case CC0:
    case PC:
    case REG:
      *total = thecosts[cost_reg];
      return true;

    case CONST_INT:
      {
	int iv = INTVAL(x);
	switch (outer_code)
	{
	  case SET: // moveq
	    if (iv >= -0x100 && iv <= 0xff)
	      {
		*total = thecosts[cost_int_moveq];
		break;
	      }
	    goto Defconst;
	  case PLUS:
	  case MINUS:
	    if (iv >= -8 && iv <= 8)
	      {
		*total = thecosts[cost_int_addq];
		break;
	      }
	    goto Defconst;
	  case ASHIFT:
	  case ASHIFTRT:
	  case LSHIFTRT:
		*total = thecosts[cost_int_addq];
	    break;
	  default:
Defconst:
	    if (iv == 0) // used in compares
	      break;

	    if ((outer_code == MEM || outer_code == COMPARE || outer_code == PLUS ||
		GET_MODE_SIZE(mode) < 4) && iv >= -32768 && iv <= 32767)
	      *total = thecosts[cost_word];
	    else
	      *total = thecosts[cost_long];
	    break;
	}
      }
      return true;

    case CONST_DOUBLE:
      *total = mode == SFmode ? thecosts[cost_float] : mode == DFmode ? thecosts[cost_double] : thecosts[cost_extended];
      return true;

    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      *total = thecosts[cost_float]; // guessed
      return true;

    case MULT:
      {
	rtx op = XEXP(x, 0);
	if (CONST_INT_P(op) && exact_log2 (INTVAL(op)))
	  total2 = thecosts[cost_shift]; // same as shift
	else
	  total2 = thecosts[cost_mult];
	goto OpCost;
      }
      break;

    case UDIV:
    case MOD:
    case DIV:
      total2 = thecosts[cost_div]; // always in a parallel with DIV and MOD -> half costs
      goto OpCost;

    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
    case PLUS:
    case MINUS:
    case AND:
    case IOR:
    case XOR:
      {
	OpCost: rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);

	// reg or mem
	m68k_68080_costs (a, mode, code, 0, total, speed);
	total2 += *total;

	// add cost for 2nd
	m68k_68080_costs (b, mode, code, 0, total, speed);
	*total += total2;
	return true;
      }
      break;

    case SUBREG:
    case STRICT_LOW_PART:
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
    case TRUNCATE:
    case ZERO_EXTEND:
    case NOT:
    case NEG:
    case SIGN_EXTEND:
    case CONST:
      // no additional cost
      return m68k_68080_costs (XEXP(x, 0), mode, code, 0, total, speed);

    case CALL:
      {
	bool r = m68k_68080_costs (XEXP(x, 0), mode, code, 0, total, speed);
	*total += thecosts[cost_call];
	return true;
      }

    case MEM:
      {
	// ADDRESS cost + 3
	bool r = m68k_68080_costs (XEXP(x, 0), mode, ADDRESS, 0, total, speed);
	*total += thecosts[cost_mem];
	return r;
      }

    case SYMBOL_REF:
    case LABEL_REF:
      *total = thecosts[cost_long];
      return true;

    case NE:
    case EQ:
    case GE:
    case GT:
    case LE:
    case LT:
    case GEU:
    case GTU:
    case LEU:
    case LTU:
    case COMPARE:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	bool r = m68k_68080_costs (dst, mode, code, 0, total, speed);
	total2 = *total;
	r &= m68k_68080_costs (src, mode, code, 0, total, speed);
	*total += total2;
	return r;
      }
    case SET:
      {
	total2 = thecosts[cost_base];

	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	if (GET_CODE(dst) == PC)
	  {
	    if (GET_CODE(src) == IF_THEN_ELSE)
	      {
		*total = thecosts[cost_if];
		return true;
	      }
	    bool r = m68k_68080_costs (src, mode, ADDRESS, 0, total, speed);
	    *total += total2;
	    return true;
	  }
	if (GET_CODE(dst) == CC0)
	  {
	    bool r = m68k_68080_costs (src, mode, code, 0, total, speed);
	    *total += total2;
	    return r;
	  }
	// big penalty for 32x32->64 mul/div
	if (m68k_tune == u68060 || m68k_tune == u68020_60)
	  {
	    if (GET_CODE (src) == MULT || GET_CODE (src) == DIV)
	      {
		if (GET_MODE (dst) == DImode)
		  {
		    *total = 100;
		    return true;
		  }
	      }
	  }

	bool r = m68k_68080_costs (dst, mode, code, 0, total, speed);
	total2 += *total;

	// binops have dst as first argument - check for binop
	const char *format = GET_RTX_FORMAT(GET_CODE(src));
	if (format && format[0] == 'e' && format[1] == 'e')
	  {
	    if (reload_completed)
	      {
		rtx p0 = XEXP(src, 0);
		if (SUBREG_P(p0))
		  p0 = XEXP(p0, 0);
		// reset cost if p0 == dst - do not add cost twice
		if (GET_CODE(src) == PLUS && !rtx_equal_p (p0, dst))
		  {
		    bool r = m68k_68080_costs (src, mode, ADDRESS, 0, total, speed);
		    *total += total2;
		    return true;
		  }
	      }
	    // modify dst with dst
	    total2 = thecosts[cost_base]; // reset to base cost
	  }

	r &= m68k_68080_costs (src, mode, MEM_P(dst) ? MEM : code, 0, total, speed);
	*total += total2;

	return r;
      }
      break;

    case IF_THEN_ELSE:
      *total = thecosts[cost_bcc]; // bcc
      return true;

    case ASM_OPERANDS:
    case ASM_INPUT:
      return false;
    }
  return false;
}
