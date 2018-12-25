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

#define BUFSIZE 40

//Lab 6: put your code here
static AS_instrList asList, Last;
static void emit(AS_instr inst);
static void munchStm(T_stm stm);
static Temp_temp munchExp(T_exp exp);
static Temp_tempList munchArgs(int cnt, T_expList args);
static Temp_tempList L(Temp_temp h, Temp_tempList t);

static string fsStr = NULL;

static Temp_tempList L(Temp_temp h, Temp_tempList t) {
  	return Temp_TempList(h, t);
}

static void emit(AS_instr inst) {
    	if(!Last)
            asList = Last = AS_InstrList(inst, NULL);
    	else
            Last = Last->tail = AS_InstrList(inst, NULL);
}

static void munchStm(T_stm stm){
    	switch(stm->kind)
	{
            case T_LABEL:
	    {
            	Temp_label LABEL = stm->u.LABEL;
            	emit(AS_Label(Temp_labelstring(LABEL), LABEL));
            	return;
            }
            case T_JUMP:
	    {
                T_exp expp = stm->u.JUMP.exp; 
                Temp_labelList jumps = stm->u.JUMP.jumps;
                emit(AS_Oper("jmp `j0", NULL, NULL, AS_Targets(jumps)));
                return;
            }
            case T_CJUMP:
	    {
            	T_relOp op = stm->u.CJUMP.op;            
		Temp_label t = stm->u.CJUMP.true;
            	Temp_temp left = munchExp(stm->u.CJUMP.left);
            	Temp_temp right = munchExp(stm->u.CJUMP.right);
                emit(AS_Oper("cmpq `s0, `s1", NULL, L(right, L(left, NULL)),NULL));
                string jstr;
                switch(op)
		{
                    case T_eq:
			jstr="je `j0";
			break;
                    case T_ne:
			jstr="jne `j0";
			break;
                    case T_lt:
			jstr="jl `j0";
			break;
                    case T_gt:
			jstr="jg `j0";
			break;
                    case T_le:
			jstr="jle `j0";
			break;
                    case T_ge:
			jstr="jge `j0";
			break;
		    case T_ult:
			jstr="jb `j0";
			break;
                    case T_ule:
			jstr="jbe `j0";
			break;
                    case T_ugt:
			jstr="ja `j0";
			break;
                    case T_uge:
			jstr="jae `j0";
			break;
                }
                emit(AS_Oper(jstr, NULL, NULL, AS_Targets(Temp_LabelList(t, NULL))));
                return;
            }
            case T_EXP:
            	munchExp(stm->u.EXP);
            	return;
            case T_MOVE:
	    {
                T_exp src = stm->u.MOVE.src;
                T_exp dst = stm->u.MOVE.dst;
                if(dst->kind == T_TEMP)
		{
                    emit(AS_Move("movq `s0, `d0", L(munchExp(dst),NULL), L(munchExp(src),NULL)));
                    return;
            	}
            	if(dst->kind == T_MEM)
		{
                    if(dst->u.MEM->kind == T_TEMP || dst->u.MEM->kind == T_CONST)
		    {
                    	emit(AS_Move("movq `s0, (`s1)", NULL,L(munchExp(src),L(munchExp(dst->u.MEM),NULL))));
                    	return;
                    }          
                    if(dst->u.MEM->kind == T_BINOP)
		    {
                    	T_exp left = dst->u.MEM->u.BINOP.left;
                    	T_exp right = dst->u.MEM->u.BINOP.right;
                    	if(right->kind != T_CONST && right->kind != T_TEMP && left->kind != T_CONST && left->kind != T_TEMP)
			{
                            emit(AS_Move("movq `s0, (`s1)", NULL ,L(munchExp(src),L(munchExp(dst->u.MEM),NULL))));
                            return;
                        }
                    	if(left->kind == T_TEMP && right->kind == T_CONST)
			{
			    char *a = checked_malloc(BUFSIZE * sizeof(char));
            		    sprintf(a,"movq `s0, %d(`s1)", right->u.CONST);
            		    emit(AS_Move(a, NULL, L(munchExp(src),L(munchExp(left),NULL))));
                            return;
                    	}
                    	if(right->kind == T_TEMP && left->kind == T_CONST)
			{
			    char *a = checked_malloc(BUFSIZE * sizeof(char));
            		    sprintf(a,"movq `s0, %d(`s1)", left->u.CONST);
            		    emit(AS_Move(a, NULL, L(munchExp(src),L(munchExp(right),NULL))));
                            return;
                    	}
                    }
            	}
            	return;
            }
	    
    	}
}

static Temp_temp munchExp(T_exp e){
    	switch(e->kind)
	{        
            case T_BINOP:
	    { 
            	T_binOp op = e->u.BINOP.op;
            	Temp_temp left = munchExp(e->u.BINOP.left);
            	Temp_temp right = munchExp(e->u.BINOP.right);
            	string opstr;
            	switch(op)
		{
               	    case T_plus:
			opstr = "addq `s1, `d0";
			break;
               	    case T_minus:
			opstr = "subq `s1, `d0";
			break;
               	    case T_mul:
			opstr = "imulq `s1, `d0";
			break;
               	    case T_div:
		    {
                   	emit(AS_Move("movq `s0, `d0",L(F_RAX(),NULL),L(left,NULL)));
			emit(AS_Oper("cqto",L(F_RAX(),L(F_RDX(), NULL)),NULL,NULL));
			emit(AS_Oper("idivq `s0", L(F_RAX(),L(F_RDX(), NULL)), L(right,NULL), NULL));
			return F_RAX();
               	    } 
            	}

            	if(e->u.BINOP.left->kind == T_TEMP)
		{
                    Temp_temp n = Temp_newtemp();
                    emit(AS_Move("movq `s0, `d0", L(n,NULL), L(left,NULL)));
                    emit(AS_Oper(opstr, L(n, NULL),L(n, L(right,NULL)), NULL));
                    return n;
            	}
            
            	emit(AS_Oper(opstr, L(left, NULL),L(left, L(right,NULL)), NULL));
            	return left;
            }
	    case T_MEM:
	    {
            	T_exp MEM = e->u.MEM;
            	Temp_temp dst = Temp_newtemp();
            	if(MEM->kind == T_TEMP)
		{
                    emit(AS_Move("movq (`s0), `d0", L(dst,NULL),L(MEM->u.TEMP,NULL)));
                    return dst;
            	}     
            	if(MEM->kind == T_CONST)
		{
                    emit(AS_Move("movq (`s0), `d0", L(dst,NULL),L(munchExp(MEM),NULL)));
                    return dst;
            	}       
            	if(MEM->kind == T_BINOP)
		{
                    T_exp left = MEM->u.BINOP.left, right = MEM->u.BINOP.right;
                    if(right->kind != T_CONST && right->kind != T_TEMP && left->kind != T_CONST && left->kind != T_TEMP)
		    {
                    	emit(AS_Move("movq (`s0), `d0", L(dst,NULL),L(munchExp(MEM),NULL)));
                    	return dst;
                    }
                    if(left->kind == T_TEMP && right->kind == T_CONST)
		    {
			char *a = checked_malloc(BUFSIZE * sizeof(char));
            		sprintf(a,"movq %d(`s0), `d0", right->u.CONST);
            		emit(AS_Move(a, L(dst,NULL), L(munchExp(left),NULL)));
                        return dst;
                    }
                    if(right->kind != T_CONST && right->kind != T_TEMP || right->kind == T_TEMP && left->kind == T_CONST)
		    {
			char *a = checked_malloc(BUFSIZE * sizeof(char));
            		sprintf(a,"movq %d(`s0), `d0", left->u.CONST);
            		emit(AS_Move(a, L(dst,NULL), L(munchExp(right),NULL)));
                        return dst;
                    }
            	}
            }
            case T_TEMP:
	    {
            	Temp_temp t = e->u.TEMP;
            	if (t == F_FP())
		{
                    t = Temp_newtemp();
    		    char *a = checked_malloc(BUFSIZE * sizeof(char));
    		    sprintf(a, "leaq %s(`s0), `d0", fsStr);
    		    emit(AS_Move(a, L(t,NULL), L(F_SP(),NULL)));
		}

           	return t;
            }
            case T_NAME:
	    {
            	Temp_temp dst = Temp_newtemp();
            	char *a = checked_malloc(BUFSIZE * sizeof(char));
            	sprintf(a,"leaq %s, `d0", Temp_labelstring(e->u.NAME));
            	emit(AS_Oper(a, L(dst, NULL), NULL, NULL));
            	return dst;
            }
	    case T_CONST:
	    {
            	Temp_temp dst = Temp_newtemp();
            	char *a = checked_malloc(BUFSIZE * sizeof(char));
            	sprintf(a, "movq $%d, `d0", e->u.CONST);
            	emit(AS_Move(a, L(dst,NULL), NULL));
            	return dst;
            }
            case T_CALL:
	    {
            	Temp_tempList regs = munchArgs(0, e->u.CALL.args);

            	char *a = checked_malloc(BUFSIZE * sizeof(char));
            	sprintf(a, "call %s", Temp_labelstring(e->u.CALL.fun->u.NAME));
            	emit(AS_Oper(a, L(F_RAX(), F_callerSave()), regs, NULL));
            	return F_RAX();
            }
    	}
}

static Temp_tempList munchArgs(int cnt, T_expList args){
    	if(!args)
            return NULL;
    
    	T_exp arg = args->head;
    	Temp_temp src = munchExp(arg), dst;

	switch(cnt)
	{
	    case 0:
		dst = F_RDI();
            	break;
	    case 1:
		dst = F_RSI();
            	break;
	    case 2:
		dst = F_RDX();
            	break;
	    case 3:
		dst = F_RCX();
            	break;
	    case 4:
		dst = F_R8();
            	break;
	    case 5:
		dst = F_R9();
            	break;
	    default:
		munchArgs(cnt+1, args->tail);
            	char *a = checked_malloc(BUFSIZE * sizeof(char));
            	sprintf(a, "movq `s0, %d(`s1)", (cnt-6)*F_wordsize);
            	emit(AS_Move(a, NULL, L(src,L(F_RSP(),NULL))));
            	return NULL;
	}
        Temp_tempList tl = Temp_TempList(dst, munchArgs(cnt+1, args->tail));
        emit(AS_Move("movq `s0, `d0", L(dst,NULL),L(src,NULL)));
        return tl;
}


AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    	asList = NULL;
    	Last = NULL; 

    	char *a = checked_malloc(BUFSIZE * sizeof(char));
    	sprintf(a, "%s_framesize", Temp_labelstring(F_name(f)));
    	fsStr = a;

    	char *begin = checked_malloc(BUFSIZE * sizeof(char));
    	sprintf(begin, "subq $%s, `d0", fsStr);
    	emit(AS_Oper(begin, L(F_RSP(),NULL), L(F_RSP(),NULL), NULL));

    	for (T_stmList sl=stmList; sl; sl = sl->tail){
            T_stm stm = sl->head;
            munchStm(stm);
    	}  

    	char *end = checked_malloc(BUFSIZE * sizeof(char));
    	sprintf(end, "addq $%s, `d0", fsStr);
    	emit(AS_Oper(end, L(F_RSP(),NULL), L(F_RSP(),NULL), NULL));

    	return F_procEntryExit2(asList);
}

