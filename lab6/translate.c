#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.
static F_fragList frags;

struct Tr_access_ 
{
	Tr_level level;
	F_access access;
};

Tr_access Tr_Access(Tr_level level, F_access access) 
{
	Tr_access temp = checked_malloc(sizeof(*temp));
	temp->level = level;
	temp->access = access;
	return temp;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
	Tr_accessList temp = checked_malloc(sizeof(*temp));
	temp->head = head;
	temp->tail = tail;
	return temp;
}

static Tr_accessList Formals(Tr_level level, F_accessList accesses) 
{
	if (accesses) 
		return Tr_AccessList(Tr_Access(level, accesses->head), Formals(level, accesses->tail)); 
	return NULL;
}

struct Tr_level_ 
{
	F_frame frame;
	Tr_level parent;
	Tr_accessList formals;
};
static Tr_level outermost = NULL;

Tr_accessList Tr_formals(Tr_level level) 
{
	return level->formals;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape) 
{
	return Tr_Access(level, F_allocLocal(level->frame, escape));
}

Tr_level Tr_outermost(void) 
{
	if (outermost)
		return outermost;
	else 
	{
		outermost = checked_malloc(sizeof(*outermost));
		outermost->frame = F_newFrame(Temp_namedlabel("tigermain"), NULL);
		outermost->parent = NULL;
		outermost->formals = NULL;
		return outermost;
	}
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) 
{
	Tr_level temp = checked_malloc(sizeof(*temp));
	temp->parent = parent;
	temp->frame = F_newFrame(name, U_BoolList(TRUE, formals));
	temp->formals = Formals(temp, F_formals(temp->frame)->tail);
	return temp;
}

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ 
{
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

struct Tr_expList_ 
{
	Tr_exp head;
	Tr_expList tail;	
};

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
	Tr_expList exps = checked_malloc(sizeof(*exps));
	exps->head = head;
	exps->tail = tail;
	return exps;
}

static T_exp staticLink(Tr_level level, Tr_level goal) 
{
	T_exp ex = T_Temp(F_FP());
	for (Tr_level cur = level; cur && cur != goal; cur = cur->parent)
		ex = F_Exp(F_formals(cur->frame)->head, ex);
	return ex;
}


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


static Tr_exp Tr_Ex(T_exp ex) 
{
	Tr_exp temp = checked_malloc(sizeof(*temp));
	temp->kind = Tr_ex;
	temp->u.ex = ex;
	return temp;
}

static Tr_exp Tr_Nx(T_stm nx) 
{
	Tr_exp temp = checked_malloc(sizeof(*temp));
	temp->kind = Tr_nx;
	temp->u.nx = nx;
	return temp;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) 
{
	Tr_exp temp = checked_malloc(sizeof(*temp));
	temp->kind = Tr_cx;
	temp->u.cx.trues = trues;
	temp->u.cx.falses = falses;
	temp->u.cx.stm = stm;
	return temp;
}

static T_exp unEx(Tr_exp e) 
{
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

static T_stm unNx(Tr_exp e) 
{
	switch(e->kind) 
	{
		case Tr_nx:
			return e->u.nx;
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_cx: 
		{
			Temp_label empty = Temp_newlabel();
			doPatch(e->u.cx.trues, empty);
			doPatch(e->u.cx.falses, empty);
			return T_Seq(e->u.cx.stm, T_Label(empty));
		}
	}
}

static struct Cx unCx(Tr_exp e) 
{
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

Tr_exp Tr_Nil() 
{
     	return Tr_Ex(T_Const(0));
}
 
Tr_exp Tr_Int(int i) 
{
     	return Tr_Ex(T_Const(i));
}

F_fragList Tr_getResult(void) 
{
	return frags;
}
	
Tr_exp Tr_String(string str) 
{
	Temp_label label = Temp_newlabel();
	F_frag head = F_StringFrag(label, str);
	frags = F_FragList(head, frags);
	return Tr_Ex(T_Name(label));
}

Tr_exp Tr_Call(Tr_level callee, Temp_label label, Tr_expList params, Tr_level caller) 
{
	T_expList exps = NULL;
	for (Tr_expList temp = params; temp; temp = temp->tail)
		exps = T_ExpList(unEx(temp->head), exps);

	return Tr_Ex(T_Call(T_Name(label), T_ExpList(staticLink(caller, callee->parent), exps)));
}

Tr_exp Tr_Op(A_oper oper, Tr_exp left, Tr_exp right, bool isString) {
	T_exp l, r;
	
	if (isString) 
	{
		l = F_externalCall("stringEqual", T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
		r = T_Const(0);
	} 
	else 
	{
		l = unEx(left);
		r = unEx(right);
	}

	switch (oper) 
	{
		case A_plusOp: 
        		return Tr_Ex(T_Binop(T_plus, l, r));
        	case A_minusOp: 
        		return Tr_Ex(T_Binop(T_minus, l, r));
        	case A_timesOp: 
        		return Tr_Ex(T_Binop(T_mul, l, r));
        	case A_divideOp: 
        		return Tr_Ex(T_Binop(T_div, l, r));
    		case A_eqOp: 
		{
			T_stm s = T_Cjump(T_eq, l, r, NULL, NULL);
  			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
        	case A_neqOp: 
		{
			T_stm s = T_Cjump(T_ne, l, r, NULL, NULL);
  			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
    		case A_ltOp: 
		{
			T_stm s = T_Cjump(T_lt, l, r, NULL, NULL);
  			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
    		case A_gtOp: 
		{
			T_stm s = T_Cjump(T_gt, l, r, NULL, NULL);
  			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
    		case A_leOp: 
		{
			T_stm s = T_Cjump(T_le, l, r, NULL, NULL);
  			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
    		case A_geOp: 
		{
			T_stm s = T_Cjump(T_ge, l, r, NULL, NULL);
  			patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  			patchList falses = PatchList(&s->u.CJUMP.false, NULL);
			return Tr_Cx(trues, falses, s);
		}
    	}

}

static T_stm createFields(Temp_temp r, int num, Tr_expList fields) 
{
	if (fields) 
		return T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(num * F_wordSize))), unEx(fields->head)), createFields(r, num-1, fields->tail)); 

	return T_Exp(T_Const(0));
}

Tr_exp Tr_Record(int num, Tr_expList fields) 
{
	Temp_temp r = Temp_newtemp();
	T_exp ex = T_Eseq(T_Move(T_Temp(r), F_externalCall("malloc", T_ExpList(T_Const(num * F_wordSize), NULL))),
		    T_Eseq(createFields(r, num-1, fields), T_Temp(r)));

    	return Tr_Ex(ex);
}

Tr_exp Tr_Seq(Tr_exp e1, Tr_exp e2) 
{
	return Tr_Ex(T_Eseq(unNx(e1), unEx(e2)));
}

Tr_exp Tr_Assign(Tr_exp var, Tr_exp exp) 
{
	return Tr_Nx(T_Move(unEx(var), unEx(exp)));
}

Tr_exp Tr_IfThenElse(Tr_exp test, Tr_exp then, Tr_exp elsee) 
{
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

Tr_exp Tr_For(Tr_access access, Tr_level level, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done) 
{
	Tr_exp var = Tr_simpleVar(access, level);
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

Tr_exp Tr_Break(Temp_label done)
{
	return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(done, NULL)));
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

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level) 
{
	T_exp fp = staticLink(level, access->level);
	T_exp ex = F_Exp(access->access, fp);
	return Tr_Ex(ex);
}

Tr_exp Tr_fieldVar(Tr_exp addr, int num) 
{
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(addr), T_Const(num * F_wordSize))));
}

Tr_exp Tr_subscriptVar(Tr_exp address, Tr_exp offset) 
{
    	return Tr_Ex(T_Mem(T_Binop(T_plus,unEx(address),T_Binop(T_mul, unEx(offset), T_Const(F_wordSize)))));
}

T_stm Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals) 
{
	T_stm stm = T_Move(T_Temp(F_RV()), unEx(body));
	F_frag head = F_ProcFrag(stm, level->frame);
	frags = F_FragList(head, frags);
}

void Tr_Func(Tr_exp body, Tr_level level) {
	Tr_procEntryExit(level, body, level->formals);
}

