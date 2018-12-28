#include <stdio.h>
#include <string.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.

F_fragList frags = NULL;

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
};

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail){
	Tr_expList l = checked_malloc(sizeof(*l));

	l->head = head;
	l->tail = tail;
	return l;
}

Tr_access Tr_Access(F_access access, Tr_level level) 
{
	Tr_access temp = checked_malloc(sizeof(*temp));
	temp->level = level;
	temp->access = access;
	return temp;
}

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {
		T_exp ex; 
		T_stm nx; 
		struct Cx cx; 
	} u;
};

static Tr_exp Tr_Ex(T_exp ex){
	Tr_exp e = checked_malloc(sizeof(*e));

	e->kind = Tr_ex;
	e->u.ex = ex;
	return e;
}

static Tr_exp Tr_Nx(T_stm nx){
	Tr_exp e = checked_malloc(sizeof(*e));

	e->kind = Tr_nx;
	e->u.nx = nx;
	return e;
}

static Tr_exp Tr_Cx(patchList trues,patchList falses,T_stm stm){
	Tr_exp e = checked_malloc(sizeof(*e));

	e->kind = Tr_cx;
	e->u.cx.trues = trues;
	e->u.cx.falses = falses;
	e->u.cx.stm = stm;

	return e;
}

static T_exp unEx(Tr_exp e){
	switch(e->kind) 
	{
	    case Tr_ex:
		return e->u.ex;
	    case Tr_cx: 
	    {
		Temp_temp r = Temp_newtemp();
		Temp_label t = Temp_newlabel(), f = Temp_newlabel();
		doPatch(e->u.cx.trues, t);
		doPatch(e->u.cx.falses, f);
		return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
			T_Eseq(e->u.cx.stm,
			 T_Eseq(T_Label(f),
			  T_Eseq(T_Move(T_Temp(r), T_Const(0)),
			   T_Eseq(T_Label(t), T_Temp(r))))));
	    }

	    case Tr_nx:
		return T_Eseq(e->u.nx, T_Const(0));
	}
}

static T_stm unNx(Tr_exp e){
	switch(e->kind)
	{
	    case Tr_ex:
		return T_Exp(e->u.ex);
	    case Tr_nx:
		return e->u.nx;
	    case Tr_cx:
		return T_Exp(unEx(e));
		
	}
}

static struct Cx unCx(Tr_exp e){
	switch(e->kind) 
	{
	    case Tr_cx:
		return e->u.cx;
	    case Tr_ex: 
	    {
		struct Cx trCx;
		trCx.stm = T_Cjump(T_ne, unEx(e), T_Const(0), NULL, NULL);
		trCx.trues = PatchList(&(trCx.stm->u.CJUMP.true), NULL);
		trCx.falses = PatchList(&(trCx.stm->u.CJUMP.false), NULL);
		return trCx;
	    }
	}
}

static Tr_level outermost = NULL;
Tr_level Tr_outermost(void) 
{
	if (outermost)
	    return outermost;
	else 
	{
	    outermost = checked_malloc(sizeof(*outermost));
	    outermost->frame = F_newFrame(Temp_namedlabel("tigermain"), NULL);
	    outermost->parent = NULL;
	    return outermost;
	}
}

static Tr_level tigermain = NULL;
Tr_level Tr_tigermain(void) 
{
	if (tigermain)
	    return tigermain;
	else 
	{
	    tigermain = checked_malloc(sizeof(*outermost));
	    tigermain->frame = F_newFrame(Temp_namedlabel("tigermain"), NULL);
	    tigermain->parent = Tr_outermost();
	    return tigermain;
	}
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals){
	Tr_level l = checked_malloc(sizeof(*l));
	U_boolList newl = U_BoolList(TRUE, formals);
	l->frame = F_newFrame(name, newl);
	l->parent = parent;
	return l;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape){
	Tr_access ac = checked_malloc(sizeof(*ac));
	ac->access = F_allocLocal(level->frame, escape);
	ac->level = level;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail){
	Tr_accessList list = checked_malloc(sizeof(*list));

	list->head = head;
	list->tail = tail;
	return list;
}

Tr_accessList makeFormalsT(F_accessList accesses, Tr_level level){
	if (!accesses)
	    return NULL;

	return Tr_AccessList(Tr_Access(accesses->head, level), makeFormalsT(accesses->tail, level));
}

Tr_accessList Tr_formals(Tr_level level){
	return makeFormalsT(F_formals(level->frame), level);
}

T_exp staticLink(Tr_level level, Tr_level goal) 
{
	T_exp ex = T_Temp(F_FP());
	for (Tr_level cur = level; cur && cur != goal; cur = cur->parent)
	    ex = F_exp(F_formals(cur->frame)->head, ex);

	return ex;
}

Tr_exp Tr_simpleVar(Tr_access acc, Tr_level l){
	return Tr_Ex(F_exp(acc->access, staticLink(l, acc->level)));
}

Tr_exp Tr_fieldVar(Tr_exp addr, int num){
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(addr), T_Const(num * F_wordSize))));
}

Tr_exp Tr_subscriptVar(Tr_exp addr, Tr_exp off){
	return Tr_Ex(T_Mem(T_Binop(T_plus,T_Binop(T_mul, T_Const(F_wordSize), unEx(off)), unEx(addr))));
}

Tr_exp Tr_Nil(){
    	return Tr_Ex(T_Const(0));
}
Tr_exp Tr_Int(int i){
    	return Tr_Ex(T_Const(i));
}
Tr_exp Tr_String(string str){
    	Temp_label label = Temp_newlabel();
	F_frag head = F_StringFrag(label, str);
	frags = F_FragList(head, frags);
	return Tr_Ex(T_Name(label));
}
Tr_exp Tr_Call(Temp_label label, Tr_expList params, Tr_level caller, Tr_level callee){
    	T_expList args = NULL;
    	int num = 0;
    	for(Tr_expList param=params; param; param=param->tail, num++)
            args = T_ExpList(unEx(param->head), args);

    	for (;num > 5;num--)
            F_allocLocal(callee->frame, TRUE);
    
    	if (!strcmp(S_name(label),"flush") || !strcmp(S_name(label),"printi") || !strcmp(S_name(label),"print") || !strcmp(S_name(label),"getchar") || !strcmp(S_name(label),"ord") || !strcmp(S_name(label),"not") || !strcmp(S_name(label),"size") || !strcmp(S_name(label),"concat") || !strcmp(S_name(label),"exit") || !strcmp(S_name(label),"chr") || !strcmp(S_name(label),"substring")) 
        return Tr_Ex(F_externalCall(S_name(label), args));
    
    	args = T_ExpList(staticLink(callee, caller->parent), args);

    	return Tr_Ex(T_Call(T_Name(label), args));
}
Tr_exp Tr_arithExp(A_oper op, Tr_exp left, Tr_exp right){
    	switch(op)
	{
            case A_plusOp:
		return Tr_Ex(T_Binop(T_plus,unEx(left),unEx(right)));
            case A_minusOp:
		return Tr_Ex(T_Binop(T_minus,unEx(left),unEx(right)));
            case A_timesOp:
		return Tr_Ex(T_Binop(T_mul,unEx(left),unEx(right)));
            case A_divideOp:
		return Tr_Ex(T_Binop(T_div,unEx(left),unEx(right)));
    	}
}
Tr_exp Tr_intCompExp(A_oper op, Tr_exp left, Tr_exp right){
    	T_relOp rop;
    	switch(op)
	{
            case A_eqOp:
		rop=T_eq;break;
            case A_neqOp:
		rop=T_ne;break;
            case A_ltOp:
		rop=T_lt;break;
            case A_leOp:
		rop=T_le;break;
            case A_gtOp:
		rop=T_gt;break;
            case A_geOp:
		rop=T_ge;break;
    	}
    	T_stm s = T_Cjump(rop, unEx(left), unEx(right),NULL, NULL);
    	patchList trues = PatchList(&(s->u.CJUMP.true),NULL);
    	patchList falses = PatchList(&(s->u.CJUMP.false),NULL);
    
    	return Tr_Cx(trues,falses,s);
}
Tr_exp Tr_strCompExp(A_oper op, Tr_exp left, Tr_exp right){
    	T_relOp rop;
    	switch(op)
	{
            case A_ltOp:case A_leOp:case A_gtOp:case A_geOp:
		return Tr_intCompExp(op, left, right);
            case A_eqOp:
		rop=T_eq;break;
            case A_neqOp:
		rop=T_ne;break;
    	}

    	T_exp func = F_externalCall("stringEqual", T_ExpList(unEx(left),T_ExpList(unEx(right),NULL)));
    	T_stm s = T_Cjump(rop, func, T_Const(1), NULL, NULL);
    	patchList trues = PatchList(&(s->u.CJUMP.true),NULL);
    	patchList falses = PatchList(&(s->u.CJUMP.false),NULL);
    	return Tr_Cx(trues,falses,s);  
}

T_stm createFields(Temp_temp r, int num, Tr_expList fields) 
{
	if (fields) 
		return T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(num * F_wordSize))), unEx(fields->head)), createFields(r, num-1, fields->tail)); 

	return T_Exp(T_Const(0));
}

Tr_exp Tr_Record(Tr_expList fields, int num) 
{
	Temp_temp r = Temp_newtemp();
	T_exp ex = T_Eseq(T_Move(T_Temp(r), F_externalCall("malloc", T_ExpList(T_Const(num * F_wordSize), NULL))),
		    T_Eseq(createFields(r, num-1, fields), T_Temp(r)));

    	return Tr_Ex(ex);
}

Tr_exp Tr_Seq(Tr_expList list){
    	T_exp e = unEx(list->head);
    	T_exp s = NULL;
    	Tr_expList p;
    	for(p=list->tail;p;p=p->tail)
	{
            if(s)
            	s = T_Eseq(unNx(p->head),s);
        
            else
            	s = T_Eseq(unNx(p->head),e);
    	}
	
    	if(!s)
            return Tr_Ex(e);
    
    return Tr_Ex(s);
}

Tr_exp Tr_Assign(Tr_exp var, Tr_exp exp) {
	return Tr_Nx(T_Move(unEx(var), unEx(exp)));
}

Tr_exp Tr_IfThenElse(Tr_exp test, Tr_exp then, Tr_exp elsee){
    	struct Cx temp = unCx(test);
	Temp_temp r = Temp_newtemp();
	Temp_label t = Temp_newlabel(), f = Temp_newlabel();
	doPatch(temp.trues, t);
	doPatch(temp.falses, f);
	if (elsee)
	{
	    Temp_label done = Temp_newlabel();
	    T_exp ex = T_Eseq(temp.stm,
			T_Eseq(T_Label(t),
			 T_Eseq(T_Move(T_Temp(r), unEx(then)),
			  T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
			   T_Eseq(T_Label(f),
			    T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
			     T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
			      T_Eseq(T_Label(done), T_Temp(r)))))))));
	    return Tr_Ex(ex);
	}
	else
	{
	    T_stm nx = T_Seq(temp.stm,
			T_Seq(T_Label(t),
			 T_Seq(unNx(then), T_Label(f))));
	    return Tr_Nx(nx);
	}
}

Tr_exp Tr_While(Tr_exp test, Tr_exp body, Temp_label done) 
{
	struct Cx temp = unCx(test);
	Temp_label t = Temp_newlabel(), b = Temp_newlabel();
	doPatch(temp.trues, b);
	doPatch(temp.falses, done);

	T_stm nx = T_Seq(T_Label(t),
		    T_Seq(temp.stm,
		     T_Seq(T_Label(b),
		      T_Seq(unNx(body),
		       T_Seq(T_Jump(T_Name(t), Temp_LabelList(t, NULL)), T_Label(done))))));

	return Tr_Nx(nx);
}

Tr_exp Tr_For(Tr_exp var, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done){
    	Temp_temp limit = Temp_newtemp();
	Temp_label b = Temp_newlabel(), inc = Temp_newlabel();

	T_stm nx = T_Seq(T_Move(unEx(var), unEx(lo)),
		    T_Seq(T_Move(T_Temp(limit), unEx(hi)),
                     T_Seq(T_Cjump(T_gt, unEx(var), T_Temp(limit), done, b),
                      T_Seq(T_Label(b),
                       T_Seq(unNx(body),
			T_Seq(T_Cjump(T_eq, unEx(var), T_Temp(limit), done, inc),
			 T_Seq(T_Label(inc),
			  T_Seq(T_Move(unEx(var), T_Binop(T_plus, unEx(var), T_Const(1))),
			   T_Seq(T_Jump(T_Name(b), Temp_LabelList(b, NULL)), T_Label(done))))))))));

	return Tr_Nx(nx);
}

Tr_exp Tr_Break(Temp_label done){
    return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(done, NULL)));
}

Tr_exp Tr_Let(Tr_expList dec, Tr_exp body){
    	T_exp e = unEx(body);
    	T_exp s = NULL;
    	for(Tr_expList p=dec;p;p=p->tail)
	{
            if(s)
            	s = T_Eseq(unNx(p->head), s);
            else
            	s = T_Eseq(unNx(p->head), e);
        }
    	if(!s)
            return body;

    	return Tr_Ex(s);
}

Tr_exp Tr_Array(Tr_exp size, Tr_exp init) 
{
	Temp_temp r;
	Temp_temp n = Temp_newtemp(), i = Temp_newtemp();

	T_exp ex = T_Eseq(T_Move(T_Temp(n), unEx(size)),
		    T_Eseq(T_Move(T_Temp(i), unEx(init)),
		     T_Eseq(T_Move(T_Temp(r), F_externalCall("initArray", T_ExpList(T_Binop(T_mul, T_Temp(n), T_Const(F_wordSize)), T_ExpList(T_Temp(i) , NULL)))), T_Temp(r))));

    	return Tr_Ex(ex);
}

Tr_exp Tr_varDec(Tr_access acc, Tr_exp init){
    	T_exp pos = unEx(Tr_simpleVar(acc, acc->level));
    	return Tr_Nx(T_Move(pos, unEx(init)));
}


void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals){
	F_frame f = level->frame;
	T_stm s = T_Move(T_Temp(F_RV()), unEx(body)); 
    	s = F_procEntryExit1(f, s);

	F_frag proc = F_ProcFrag(s, f);

	frags = F_FragList(proc, frags);
}

F_fragList Tr_getResult(void){
    	return frags;
}
