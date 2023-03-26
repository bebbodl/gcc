#define IN_TARGET_CODE 1

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "cfghooks.h"
#include "tree.h"
#include "rtl.h"

/**
 * calculate costs for the 68040.
 * opno == 1: calculate as if dst is a register
 * opno == 0: calculate difference to register assignment
 */
bool
__m68k_68040_costs (rtx x, machine_mode mode, int outer_code ATTRIBUTE_UNUSED, int opno ATTRIBUTE_UNUSED,
		  int *total, bool speed)
{
  int code = GET_CODE(x);
  int total2 = 0;
  *total = 0;
  switch (code)
    {
    case CALL:
      {
	rtx a = XEXP(x, 0);
	if (MEM_P(a))
	  {
	    rtx b = XEXP(a, 0);
	    if (REG_P(b) || GET_CODE(b) == PC)
	      {
		*total = 6;
      return true;
	      }
	    if (GET_CODE(b) == PLUS)
	      {
		if (REG_P(XEXP(b, 0)))
		  {
		    *total = 8;
		    return true;
		  }
	      }
	    else if (SYMBOL_REF_P(b) || GET_CODE(b) == CONST_INT)
	      {
//		tree decl = SYMBOL_REF_DECL(b);

		*total = 6;
      return true;
	      }
	  }
	*total = 12;
	return true;
      }
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
      return __m68k_68040_costs (XEXP(x, 0), mode, code, 0, total, speed);
    case CONST:
		*total = 1;
		return true;
	  break;
    case LABEL_REF:
    case SYMBOL_REF:
      *total = 1;
      return true;
    case CONST_INT:
      *total = 0;
      return true;
    case CONST_DOUBLE:
      *total = GET_MODE_SIZE(mode) > 4 ? 2 : 1;
      return true;
    case POST_INC:
      *total = 0;
      return true;
    case PRE_DEC:
      *total = 0;
      return true;
    case REG:
    case SUBREG:
    case STRICT_LOW_PART:
    case PC:
      *total = 0;
      return true;
    case SIGN_EXTRACT:
    case ZERO_EXTRACT:
      *total = 4;
      return true;
    case TRUNCATE:
    case ZERO_EXTEND:
      *total = 1;
      return true;
    case NOT:
    case NEG:
    case SIGN_EXTEND:
      *total = 1;
      return true;
    case UDIV:
      *total = GET_MODE_SIZE(mode) > 2 ? 44 : 27;
      return true;
    case MOD:
    case DIV:
      *total = GET_MODE_SIZE(mode) > 2 ? 44 : 27;
      return true;
    case MEM:
      {
	rtx a = XEXP(x, 0);
	if (REG_P(a))
	  {
	    *total = 1;
	    return true;
	  }
	if (GET_CODE(a) == POST_INC)
	  {
	    *total = 1;
	    return true;
	  }
	if (GET_CODE(a) == PRE_DEC)
	  {
	    *total = 1;
	    return true;
	  }
	if (GET_CODE(a) == PLUS)
	  {
	    rtx b = XEXP(a, 0);
	    rtx c = XEXP(a, 1);
	    if (REG_P(b) && (GET_CODE(c) == CONST_INT || GET_CODE(c) == SYMBOL_REF))
	      {
		*total = 2 + ((GET_CODE(c) == CONST_INT && IN_RANGE(INTVAL(c), -32786, 32767)) ? 0 : 1);
		return true;
	      }
	    if (REG_P(b) && REG_P(c))
	      {
		*total = 3;
		return true;
	      }
	  }
	*total = 4;
	return true;
      }
      break;
    case SET:
      {
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);
	if (REG_P(dst) //|| GET_CODE(dst) == CC0
			)
		  {
	    if (__m68k_68040_costs (src, mode, code, 1, total, speed))
		    return true;
		  }
	else if (__m68k_68040_costs (dst, mode, code, 0, total, speed)
	    && __m68k_68040_costs (src, mode, code, 1, &total2, speed))
	  {
	    *total += total2;
	    return true;
	  }
      }
      break;
    case PLUS:
    case MINUS:
    case AND:
    case IOR:
    case XOR:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	if (__m68k_68040_costs (a, mode, code, 0, total, speed)
	    && __m68k_68040_costs (b, mode, code, 1, &total2, speed))
	  {
	    *total += total2;
	    // for lea
	    if (GET_CODE (a) == PLUS && REG_P (XEXP (a, 1)))
	      *total += 3;
	    return true;
	  }
      }
      break;
    case ASHIFT:
    case ASHIFTRT:
    case LSHIFTRT:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	if (REG_P(a))
	  {
	    if (GET_CODE(b) == CONST_INT)
	      {
		*total = 2;
		return true;
	      }
	      *total = 3;
	      return true;
	  }
	*total = 4;
	if (CONST_INT_P(b))
	  {
	    int n = INTVAL(b);
	    if (n > 8)
	      *total += 4;
	  }
	return true;
      }
      break;
    case MULT:
      {
	/* umul, smul or call to __mulsi3? */
	rtx dst = XEXP(x, 0);
	rtx src = XEXP(x, 1);

	if (GET_CODE(src) == CONST_INT)
	  {
	    int i = INTVAL(src);
	    int bits = 0, l = 0;
	    if (i > 0)
	      {
		if (GET_CODE (dst) == ZERO_EXTEND || REG_P(dst))
		  {
		    while (i)
		      {
			if (i & 1)
			  ++bits;
			i >>= 1;
		      }
		    // it's a shift
		    if (bits == 1 && REG_P(dst))
		      {
			*total = 3;
			return true;
		      }
		  }
		else
		  // SIGN_EXTEND
		  while (i || l)
		    {
		      if ((i & 1) != l)
			{
			  l = !l;
			  ++bits;
			}
		      i >>= 1;
		    }

		*total = 4 + bits/2;
		return true;
	      }
	  }

	*total = GET_MODE_SIZE(mode) > 2 ? 20 : 16;
	return true;
      }
      break;
    case COMPARE:
      {
	rtx a = XEXP(x, 0);
	rtx b = XEXP(x, 1);
	if (REG_P(a))
	  {
	    if (GET_CODE(b) == CONST_INT)
	      {
		*total = 0;
		return true;
	      }
	    __m68k_68040_costs (b, mode, code, 1, total, speed);
	    return true;
	  }
	if (__m68k_68040_costs (a, mode, code, 0, total, speed))
	  {
	    if (GET_CODE(b) == CONST_INT && INTVAL(b) == 0)
	      return true;

	    if (__m68k_68040_costs (b, mode, code, 1, &total2, speed))
	      {
	    *total += total2;
	    return true;
	  }
      }
      }
      break;
    case IF_THEN_ELSE:
      *total = 3;
      return true;
    case FLOAT:
    case FLOAT_TRUNCATE:
    case FIX:
      // maybe check for 68881?
      *total = 2;
      return true;
    case ASM_OPERANDS:
    case ASM_INPUT:
      return false;
    }
  *total = 1;
//  fprintf (stderr, "%d: ", outer_code);
//  debug_rtx (x);
  return true;
}

bool
m68k_68040_costs (rtx x, machine_mode mode, int outer_code, int opno,
		  int *total, bool speed) {
  bool r = __m68k_68040_costs(x, mode, outer_code, opno, total, speed);

  if (r) *total = COSTS_N_INSNS(*total ? *total : 1);

  return r;
}

