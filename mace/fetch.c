/*
 * Giovanni Agosta, Andrea Di Biagio
 * Politecnico di Milano, 2007
 * 
 * fetch.c
 * Formal Languages & Compilers Machine, 2007/2008
 * 
 */
#include <stdlib.h>
#include <limits.h>
#include "decode.h"
#include "fetch.h"
#include "machine.h"

#define MAX(X,Y) ((X) > (Y) ? (X) : (Y) )
#define SIGN(X) ((X) >= 0?1:0)
#define MSB(X) (((X) >> 31)&1)


static int executeTER(decoded_instr *instr);
static int executeBIN(decoded_instr *instr);
static int executeUNR(decoded_instr *instr);
static int executeJMP(decoded_instr *instr);
static int handle_special_instruction(decoded_instr *instr);
static int perform_add(int sign, int a, int b, int *carry, int *overflow);
static int perform_sub(int sign, int a, int b, int *carry, int *overflow);
static int perform_rotl(int value, int amount, int *carry);
static int perform_rotr(int value, int amount, int *carry);

/* returns next pc, negative values are error codes, 0 is correct termination */
int fetch_execute(unsigned int *code, int pc){
   int result;
	decoded_instr *instr = decode(code[pc]);
	switch (instr->format) {
		case TER : result = executeTER(instr);
			break;
		case BIN : result = executeBIN(instr);
			break;
		case UNR : result = executeUNR(instr);
			break;
		case JMP : result = executeJMP(instr);
			break;
		default : result = INVALID_INSTR_FORMAT;
	}

   /* free the memory associated with `instr' */
   if (instr != NULL)
      free(instr);

   /* return the new PC (or the value _HALT) as result */
   return result;
}

int executeTER(decoded_instr *instr){
	int *dest, *src1, *src2;
    int old_dest, old_src1, old_src2;
	int carryout=0, overflow=0, negative=0, zero=0;
    long long int mulresult;

	/* Manage addressing modes (direct/indirect) */
	if (indirect_dest(instr)) dest=&(mem[reg[instr->dest]]);
	else dest=&(reg[instr->dest]);
	src1=&(reg[instr->src1]);
	if (indirect_src2(instr)) src2=&(mem[reg[instr->src2]]);
	else src2=&(reg[instr->src2]);

    old_dest = *dest;
    old_src1 = *src1;
    old_src2 = *src2;

   switch (instr->opcode) {
        case ADD  :
            *dest = perform_add(sign(instr), *src1, *src2, &carryout, &overflow);
            if (carry(instr) && getflag(CARRY)) *dest = perform_add(sign(instr), *dest, 1, &carryout, &overflow);
        break;
        case SUB  :
            * dest= perform_sub(sign(instr), *src1, *src2, &carryout, &overflow);
            if (carry(instr) && getflag(CARRY)) *dest = perform_sub(sign(instr), *src1, 1, &carryout, &overflow);
		 break;
		case ANDL : *dest = *src1 && *src2 ;
		 break;
		case ORL  : *dest = *src1 || *src2 ;
		 break;
		case EORL : *dest = (*src1 && !*src2) || (!*src1 && *src2);
		 break;
		case ANDB : *dest = *src1 & *src2 ;
		 break;
		case ORB  : *dest = *src1 | *src2 ;
		 break;
		case EORB : *dest = *src1 ^ *src2 ;
		 break;
        case MUL  :
            if (sign(instr)) {
                mulresult = (long long)*src1 * (long long)*src2;
                if ((mulresult >> 32) != 0 && ((mulresult >> 32)&UINT_MAX) != UINT_MAX) overflow = 1;
                if (SIGN(mulresult) != SIGN((int)(mulresult >> 32))) overflow = 1;
			} else {
                mulresult = (long long)((unsigned)*src1) * (long long)((unsigned)*src2);
                if (mulresult >> 32) carryout = 1;
			}
            *dest = mulresult & UINT_MAX;
            if (carry(instr) && getflag(CARRY)) *dest = perform_add(sign(instr), *dest, 1, &carryout, &overflow);
		 break;
        case DIV  :
            if (sign(instr)) {
                *dest = *src1 / *src2;
                if (old_src1 == INT_MIN && old_src2 == -1) overflow = 1;
			} else {
                *dest = ((unsigned)*src1) / ((unsigned)*src2);
			}
            if (carry(instr) && getflag(CARRY)) *dest = perform_sub(sign(instr), *dest, 1, &carryout, &overflow);
		 break;
        case SHL  : 
            if(old_src2 > 32) {
                *dest = 0;
            } else {
                *dest = *src1 << *src2;
                carryout = !!(old_src1 & (1 << (32 - old_src2)));
            }
            if (carry(instr) && getflag(CARRY)) *dest = perform_add(sign(instr), *dest, 1, &carryout, &overflow);
		 break;
        case SHR  :
            *dest = *src1 >> *src2;
            if (sign(instr) && !SIGN(old_src1)) {
                /* Arithmetic shift */
                *dest |= ((1 << old_src2) - 1) << MAX(32 - old_src2, 0);
            }
            else if(!sign(instr)) {
                /* Logic shift */
                *dest &= (1 << MAX(32 - old_src2, 0)) - 1;
            }
            if(old_src2) {
                if(old_src2 > 32) carryout = (sign(instr) && !SIGN(old_src1));
                else carryout = !!(old_src1 & (1 << old_src2 - 1));
            }
            if (carry(instr) && getflag(CARRY)) *dest = perform_add(sign(instr), *dest, 1, &carryout, &overflow);
		 break;
        case ROTL : *dest = perform_rotl(*src1, *src2, &carryout);
		 break;
        case ROTR : *dest = perform_rotr(*src1, *src2, &carryout);
		 break;
		case NEG  : *dest = - *src2;
            if (sign(instr) && old_src2 == INT_MIN) overflow = 1;
            if (carry(instr) && getflag(CARRY)) *dest = perform_sub(sign(instr), *dest, 1, &carryout, &overflow);
		 break;
		case SPCL : pc=handle_special_instruction(instr) ;
		 break;
		default :
         return INVALID_INSTR;
	}
	zero = (*dest == 0);
	negative = (*dest < 0);

	setflag(CARRY,carryout);
	setflag(OVERFLOW,overflow);
	setflag(ZERO,zero);
	setflag(NEGATIVE,negative);

	return pc+1;
}

int executeBIN(decoded_instr *instr)
{
	int *dest, *src1, *src2;
        int old_dest, old_src1, old_src2;
	int carryout=0, overflow=0, negative=0, zero=0;
        long long int mulresult;

	/* Manage addressing modes (direct only) */
	dest=&(reg[instr->dest]);
	src1=&(reg[instr->src1]);
	src2=&(instr->imm);


    old_dest = *dest;
    old_src1 = *src1;
    old_src2 = *src2;

	switch (instr->opcode) {
        case ADDI  : *dest = perform_add(1, *src1, *src2, &carryout, &overflow);
		 break;
        case SUBI  : *dest = perform_sub(1, *src1, *src2, &carryout, &overflow);
		 break;
		case ANDLI : *dest = *src1 && *src2 ;
		 break;
		case ORLI  : *dest = *src1 || *src2 ;
		 break;
		case EORLI : *dest = (*src1 && !*src2) || (!*src1 && *src2);
		 break;
		case ANDBI : *dest = *src1 & *src2 ;
		 break;
		case ORBI  : *dest = *src1 | *src2 ;
		 break;
		case EORBI : *dest = *src1 ^ *src2 ;
		 break;
        case MULI  :
            mulresult = (long long)*src1 * (long long)*src2;
            if ((mulresult >> 32) != 0 && ((mulresult >> 32)&UINT_MAX) != UINT_MAX) overflow = 1;
            if (SIGN(mulresult) != SIGN((int)(mulresult >> 32))) overflow = 1;
            *dest = mulresult & UINT_MAX;
		 break;
		case DIVI  : *dest=*src1 / *src2; 
            if (old_src1 == INT_MIN && old_src2 == -1) overflow = 1;
		 break;
        case SHLI  :
            if(old_src2 > 32) {
                *dest = 0;
            } else {
                *dest = *src1 << *src2;
                carryout = !!(old_src1 & (1 << (32 - old_src2)));
            }
		 break;
		case SHRI  : *dest = *src1 >> *src2; 
            if (!SIGN(old_src1)) {
                /* Arithmetic shift */
                *dest |= ((1 << old_src2) - 1) << MAX(32 - old_src2, 0);
            }
            if(old_src2) {
                if(old_src2 > 32) carryout = (sign(instr) && !SIGN(old_src1));
                else carryout = !!(old_src1 & (1 << old_src2 - 1));
            }
		 break;
        case ROTLI: *dest = perform_rotl(*src1, *src2, &carryout);
		 break;
        case ROTRI: *dest = perform_rotr(*src1, *src2, &carryout);
		 break;
		case NOTL : *dest = !*src1 ;
		 break;
		case NOTB : *dest = ~*src1 ;
		 break;
		default : return INVALID_INSTR;
	}

	zero = (*dest == 0);
	negative = (*dest < 0);

	setflag(CARRY,carryout);
	setflag(OVERFLOW,overflow);
	setflag(ZERO,zero);
	setflag(NEGATIVE,negative);
	
	return pc+1;
}

int executeUNR(decoded_instr *instr){
	int *dest, src ;

	/* Manage addressing modes (direct only) */
	dest=&reg[instr->dest];
	src=instr->addr;

	switch (instr->opcode) {
		case NOP : /* NOP */
			break;
		case HALT : /* HALT */
			return _HALT;
			break;
		case MOVA : *dest = src ; /* Move a 20-bit constant to a register */
			break;
      case LOAD : *dest = mem[src];
         break;
      case STORE : mem[src] = *dest;
         break;
		case JSR : /* Not implemented yet */ ;
			break;
		case RET : /* Not implemented yet */ ;
			break;
      case SEQ :  *dest = getflag(ZERO);
                  setflag(ZERO, (*dest == 0));
                  setflag(NEGATIVE, 0);
                  setflag(CARRY, 0);
                  setflag(OVERFLOW, 0);
                  break;
      case SGT :  *dest = ( ( getflag(NEGATIVE) && getflag(OVERFLOW)
                              && (!getflag(ZERO)))
                           || (!getflag(NEGATIVE) && !getflag(OVERFLOW)
                              && !getflag(ZERO)) );
                  setflag(ZERO, (*dest == 0));
                  setflag(NEGATIVE, 0);
                  setflag(CARRY, 0);
                  setflag(OVERFLOW, 0);
                  break;
      case SGE :  *dest = ((getflag(NEGATIVE) && getflag(OVERFLOW))
                           || (!getflag(NEGATIVE) && !getflag(OVERFLOW)));
                  setflag(ZERO, (*dest == 0));
                  setflag(NEGATIVE, 0);
                  setflag(CARRY, 0);
                  setflag(OVERFLOW, 0);
                  break;
      case SLE :  *dest = (getflag(ZERO) || (getflag(NEGATIVE) && !getflag(OVERFLOW))
                               || (!getflag(NEGATIVE) && getflag(OVERFLOW)));
                  setflag(ZERO, (*dest == 0));
                  setflag(NEGATIVE, 0);
                  setflag(CARRY, 0);
                  setflag(OVERFLOW, 0);
                  break;
      case SLT :  *dest = ( (getflag(NEGATIVE) && !getflag(OVERFLOW))
                               || (!getflag(NEGATIVE) && getflag(OVERFLOW)));
                  setflag(ZERO, (*dest == 0));
                  setflag(NEGATIVE, 0);
                  setflag(CARRY, 0);
                  setflag(OVERFLOW, 0);
                  break;
      case SNE :  *dest = !getflag(ZERO);
                  setflag(ZERO, (*dest == 0));
                  setflag(NEGATIVE, 0);
                  setflag(CARRY, 0);
                  setflag(OVERFLOW, 0);
                  break;
      case READ : fputs("int value? >", stdout);
                  fscanf(stdin, "%d", dest);
         break;
      case WRITE : fprintf(stdout, "%d\n", (*dest) );
         break;
		default : return INVALID_INSTR;
	}

   /* update the value of program counter */
	return pc+1;
}

int executeJMP(decoded_instr *instr){
	/*
	 * Handles Bcc instructions 
	 * (see M68000 docs for an overview of the possible branches)
	 */
	int src;
   int taken;

   /* initialize src */
   src = instr->addr;
   taken = 0;
   
	switch (instr->opcode) {
		case BT : if (1) taken = 1;
			break;
		case BF : if (0) taken = 1;
			break;
		case BHI : if (!(getflag(CARRY)||getflag(ZERO))) taken = 1;
			break;
		case BLS : if (getflag(CARRY)||getflag(ZERO)) taken = 1;
			break;
		case BCC : if (!getflag(CARRY)) taken = 1;
			break;
		case BCS : if (getflag(CARRY)) taken = 1;
			break;
		case BNE : if (!getflag(ZERO)) taken = 1;
			break;
		case BEQ : if (getflag(ZERO)) taken = 1;
			break;
		case BVC : if (!getflag(OVERFLOW)) taken = 1;
			break;
		case BVS : if (getflag(OVERFLOW)) taken = 1;
			break;
		case BPL : if (!getflag(NEGATIVE)) taken = 1;
			break;
		case BMI : if (getflag(NEGATIVE)) taken = 1;
			break;
		case BGE : if (!(getflag(NEGATIVE)^getflag(OVERFLOW))) taken = 1;
			break;
		case BLT : if (getflag(NEGATIVE)^getflag(OVERFLOW)) taken = 1;
			break;
		case BGT : if (   !(getflag(ZERO)
                        ||(getflag(NEGATIVE)^getflag(OVERFLOW)))) taken = 1;
			break;
		case BLE : if (getflag(ZERO)||(getflag(NEGATIVE)^getflag(OVERFLOW))) taken = 1;
			break;
		default : return INVALID_INSTR;
	}

   /* test if the branch is taken or not */
   if (taken)
	   pc += src;
   else
      pc++;

   return pc;
}


int handle_special_instruction(decoded_instr *instr){
	/* here should be inserted code to handle special instructions
	 * using the function bits
	 */
	return INVALID_INSTR;
}


static int perform_add(int sign, int a, int b, int *carry, int *overflow) {
    int result = a + b;
    if (sign) {
        if (SIGN(result) != SIGN(a) && SIGN(a) == SIGN(b)) *overflow = 1;
    }
    else {
        if (MSB(result) < MSB(a) + MSB(b)) { *carry = 1; }
    }
    return result;
}
static int perform_sub(int sign, int a, int b, int *carry, int *overflow) {
    int result = a - b;
    if (sign) {
        if (SIGN(result) != SIGN(a) && SIGN(a) != SIGN(b)) *overflow = 1;
    }
    else {
        if (MSB(result) > MSB(a) + MSB(b)) { *carry = 1; }
    }
    return result;
}
static int perform_rotl(int value, int amount, int *carry) {
    int result;
    int amount_mask;
    amount &= 31;
    amount_mask = (1 << amount) - 1;
    result =  value << amount;
    result |= (value >> (32 - amount)) & amount_mask;
    *carry = amount && (result & 1);
    return result;
}
static int perform_rotr(int value, int amount, int *carry) {
    int result;
    int amount_mask;
    int inv_mask;
    amount &= 31;
    amount_mask = (1 << amount) - 1;
    inv_mask = (1 << (32 - amount)) - 1;
    result = (value >> amount) & inv_mask;
    result |= (value & amount_mask) << (32 - amount);
    *carry = amount && MSB(result);
    return result;
}
