#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

//Lab 6: put your code here

#define BUFSIZE 40

static AS_instrList iList=NULL, last=NULL;
static void munchStm(T_stm s);
static Temp_temp munchExp(T_exp e);
static void munchArgs(T_expList args);

static void emit(AS_instr inst){
	if (last != NULL)
	    last = last->tail = AS_InstrList(inst,NULL);
	else
	    last = iList = AS_InstrList(inst,NULL);
}

Temp_tempList L(Temp_temp h, Temp_tempList t){
	return Temp_TempList(h,t);
}

static void munchArgs(T_expList args) {
  	T_expList rargs = NULL;
  	for(; args; args = args->tail)
    	    rargs = T_ExpList(args->head, rargs);

  	for(int i=0; rargs; rargs = rargs->tail, i++)
	{
	    switch (i)
	    {
		case 0:
		{
		    Temp_temp r = Temp_newtemp();
		    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RDI(), NULL)));
		    emit(AS_Move("movq `s0, `d0", L(F_RDI(), NULL), L(munchExp(rargs->head), NULL)));
		    break;
		}
		case 1:
		{
		    Temp_temp r = Temp_newtemp();
		    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RSI(), NULL)));
		    emit(AS_Move("movq `s0, `d0", L(F_RSI(), NULL), L(munchExp(rargs->head), NULL)));
		    break;
		}
		case 2:
		{
		    Temp_temp r = Temp_newtemp();
		    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RDX(), NULL)));
		    emit(AS_Move("movq `s0, `d0", L(F_RDX(), NULL), L(munchExp(rargs->head), NULL)));
		    break;
		}
		case 3:
		{
		    Temp_temp r = Temp_newtemp();
		    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RCX(), NULL)));
		    emit(AS_Move("movq `s0, `d0", L(F_RCX(), NULL), L(munchExp(rargs->head), NULL)));
		    break;
		}
		case 4:
		{
		    Temp_temp r = Temp_newtemp();
		    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_R8(), NULL)));
		    emit(AS_Move("movq `s0, `d0", L(F_R8(), NULL), L(munchExp(rargs->head), NULL)));
		    break;
		}
		case 5:
		{
		    Temp_temp r = Temp_newtemp();
		    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_R9(), NULL)));
		    emit(AS_Move("movq `s0, `d0", L(F_R9(), NULL), L(munchExp(rargs->head), NULL)));
		    break;
		}
		default:
		    emit(AS_Oper("push `s0", NULL, L(munchExp(rargs->head), NULL), NULL));
	    }
	}
}

static Temp_temp munchExp(T_exp e) {
	switch(e->kind) 
	{
	    case T_MEM: 
	    {
      		Temp_temp r = Temp_newtemp();
      		emit(AS_Oper("movq (`s0), `d0", L(r, NULL), L(munchExp(e->u.MEM), NULL), NULL));
      		return r;
    	    }
    	    case T_BINOP: 
	    {
      		Temp_temp left = munchExp(e->u.BINOP.left), right = munchExp(e->u.BINOP.right);
      		Temp_temp r = Temp_newtemp();
      		switch(e->u.BINOP.op) 
		{
		    case T_plus:
          	    	emit(AS_Oper("addq `s0, `d0", L(left, NULL), L(left, L(right, NULL)), NULL));
          	    	return r;
        	    case T_minus:
          		emit(AS_Oper("subq `s0, `d0", L(left, NULL), L(left, L(right, NULL)), NULL));
          		return r;
       	 	    case T_mul:
          		emit(AS_Oper("imulq `s0, `d0", L(left, NULL), L(left, L(right, NULL)), NULL));
          		return r;
        	    case T_div: 
          		emit(AS_Move("movq `s0, `d0", L(F_RAX(), NULL), L(left, NULL)));
          		emit(AS_Oper("cltd", L(F_RDX(), L(F_RAX(), NULL)), L(F_RAX(), NULL), NULL));
          		emit(AS_Oper("idivq `s0", L(F_RDX(), L(F_RAX(), NULL)), L(right, L(F_RDX(), L(F_RAX(), NULL))), NULL));
          		emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RAX(), NULL)));
          	        return r;
        	    default:
          	    	assert(0);
      		}
    	    }
    	    case T_TEMP:
      		return e->u.TEMP;
    	    case T_NAME: 
	    {
      		Temp_temp r = Temp_newtemp();
      		char *a = checked_malloc(BUFSIZE * sizeof(char));
      		sprintf(a, "movq $%s, `d0", Temp_labelstring(e->u.NAME));
      		emit(AS_Oper(a, L(r, NULL), NULL, NULL));
      		return r;
    	    }
    	    case T_CONST: 
	    {
      		Temp_temp r = Temp_newtemp();
      		char *a = checked_malloc(BUFSIZE * sizeof(char));
      		sprintf(a, "movq $%d, `d0", e->u.CONST);
      		emit(AS_Oper(a, L(r, NULL), NULL, NULL));
      		return r;
    	    }
    	    case T_CALL: 
	    {
      		if(e->u.CALL.fun->kind == T_NAME) 
		{
        	    Temp_temp r = Temp_newtemp();
        	    munchArgs(e->u.CALL.args);
        	    char *a = checked_malloc(BUFSIZE * sizeof(char));
        	    sprintf(a, "call %s", Temp_labelstring(e->u.CALL.fun->u.NAME));
        	    emit(AS_Oper(a, F_callersaves(), NULL, NULL));

        	    int offset = 0;
        	    for(T_expList args = e->u.CALL.args; args; args = args->tail)
          		offset ++;

        	    if(offset > 6) 
		    {
          		a = checked_malloc(BUFSIZE * sizeof(char));
          		sprintf(a, "addq $%d, %%rsp", (offset - 6) * F_wordSize);
          		emit(AS_Oper(a, NULL, NULL, NULL));
        	    }

        	    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RV(), NULL)));
        	    return r;
      		}
		else
        	    assert(0);
    	    }
    	    case T_ESEQ: 
	    {
      		munchStm(e->u.ESEQ.stm);
      		return munchExp(e->u.ESEQ.exp);
    	    }
   	    default:
      		assert(0);
  	}
}

static void munchStm(T_stm s){
	switch(s->kind)
	{
	    case T_MOVE:
	    {
		T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
		if (dst->kind == T_MEM)
		{
		    if (dst->u.MEM->kind == T_BINOP && dst->u.BINOP.op == T_plus && dst->u.MEM->u.BINOP.right->kind == T_CONST)
		    {
			T_exp e1 = dst->u.MEM->u.BINOP.left, e2 = src;
            		int n = dst->u.MEM->u.BINOP.right->u.CONST;
            		char *a = checked_malloc(BUFSIZE * sizeof(char));
            		sprintf(a, "movq `s0, %d(`s1)", n);
            		emit(AS_Oper(a, NULL, L(munchExp(e2), L(munchExp(e1), NULL)), NULL));
		    }
		    else if (dst->u.MEM->kind == T_BINOP && dst->u.BINOP.op == T_plus && dst->u.MEM->u.BINOP.left->kind == T_CONST)
		    {
			T_exp e1 = dst->u.MEM->u.BINOP.left, e2 = src;
            		int n = dst->u.MEM->u.BINOP.left->u.CONST;
            		char *a = checked_malloc(BUFSIZE * sizeof(char));
            		sprintf(a, "movq `s0, %d(`s1)", n);
            		emit(AS_Oper(a, NULL, L(munchExp(e2), L(munchExp(e1), NULL)), NULL));
		    }
		    else
		    {
			T_exp e1 = dst->u.MEM, e2 = src;
          		emit(AS_Oper("movl `s0, (`s1)", NULL, L(munchExp(e2), L(munchExp(e1), NULL)), NULL));
		    }
		}
		else if (dst->kind == T_TEMP)
		{
		    if(src->kind == T_CONST) 
		    {
          	    	char *a = checked_malloc(BUFSIZE * sizeof(char));
          		sprintf(a, "movq $%d, `d0", src->u.CONST);
          		emit(AS_Oper(a, L(munchExp(dst), NULL), NULL, NULL));
        	    }
        	    else if(src->kind == T_NAME) 
		    {
          		char *a = checked_malloc(BUFSIZE * sizeof(char));
          		sprintf(a, "movq $%s, `d0", Temp_labelstring(src->u.NAME));
          		emit(AS_Oper(a, L(munchExp(dst), NULL), NULL, NULL));
        	    }
        	    else 
          		emit(AS_Move("movq `s0, `d0", L(munchExp(dst), NULL), L(munchExp(src), NULL)));
		}
		else
		    assert(0);
		break;
	    }
	    case T_JUMP: 
	    {
      		T_exp e = s->u.JUMP.exp;
      		if(e->kind == T_NAME) 
		{
        	    char *a = checked_malloc(BUFSIZE * sizeof(char));
        	    sprintf(a, "jmp %s", Temp_labelstring(e->u.NAME));
        	    emit(AS_Oper(a, NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
      		}
		else
        	    assert(0);
      		break;
    	    }
    	    case T_CJUMP: 
	    {
      		string funcode;
      		Temp_temp left = munchExp(s->u.CJUMP.left);
      		Temp_temp right = munchExp(s->u.CJUMP.right);
      		switch(s->u.CJUMP.op)
		{
        	    case T_eq:
          	    	funcode = "je";
          	    	break;
       		    case T_ne:
          		funcode = "jne";
          		break;
        	    case T_lt:
          		funcode = "jl";
          		break;
        	    case T_gt:
          		funcode = "jg";
          		break;
        	    case T_le:
          		funcode = "jle";
          		break;
        	    case T_ge:
          		funcode = "jge";
          		break;
        	    default:
          		assert(0);
      		}
      		emit(AS_Oper("cmp `s0, `s1", NULL, L(right, L(left, NULL)), NULL));
      		char *a = checked_malloc(BUFSIZE * sizeof(char));
      		sprintf(a, "%s `j0",funcode);
      		emit(AS_Oper(a, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
      	    	break;
    	    }
    	    case T_EXP:
      	    	munchExp(s->u.EXP);
      		break;
    	    case T_LABEL: 
	    {
      		char *a = checked_malloc(BUFSIZE * sizeof(char));
      		sprintf(a, "%s", Temp_labelstring(s->u.LABEL));
      		emit(AS_Label(a, s->u.LABEL));
      		break;
    	    }
    	    case T_SEQ:
      		munchStm(s->u.SEQ.left);
      		munchStm(s->u.SEQ.right);
      		break;
    	    default:
      		assert(0);
	}
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
	AS_instrList list;

	Temp_temp saved_rbx = Temp_newtemp();
  	Temp_temp saved_r12 = Temp_newtemp();
  	Temp_temp saved_r13 = Temp_newtemp();
	Temp_temp saved_r14 = Temp_newtemp();
	Temp_temp saved_r15 = Temp_newtemp();

	emit(AS_Move("movq `s0, `d0", L(saved_rbx, NULL), L(F_RBX(), NULL)));
  	emit(AS_Move("movq `s0, `d0", L(saved_r12, NULL), L(F_R12(), NULL)));
  	emit(AS_Move("movq `s0, `d0", L(saved_r13, NULL), L(F_R13(), NULL)));
	emit(AS_Move("movq `s0, `d0", L(saved_r14, NULL), L(F_R14(), NULL)));
	emit(AS_Move("movq `s0, `d0", L(saved_r15, NULL), L(F_R15(), NULL)));

	for (T_stmList sl = stmList; sl; sl = sl->tail)
    	    munchStm(sl->head);

	emit(AS_Move("movq `s0, `d0", L(F_RBX(), NULL), L(saved_rbx, NULL)));
  	emit(AS_Move("movq `s0, `d0", L(F_R12(), NULL), L(saved_r12, NULL)));
  	emit(AS_Move("movq `s0, `d0", L(F_R13(), NULL), L(saved_r13, NULL)));
	emit(AS_Move("movq `s0, `d0", L(F_R14(), NULL), L(saved_r14, NULL)));
	emit(AS_Move("movq `s0, `d0", L(F_R15(), NULL), L(saved_r15, NULL)));

  	emit(AS_Oper("leave", NULL, L(F_RV(), F_calleesaves()), NULL));
  	emit(AS_Oper("ret", NULL, L(F_RV(), F_calleesaves()), NULL));

	return iList;
}
