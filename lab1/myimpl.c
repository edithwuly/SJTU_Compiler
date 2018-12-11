#include "prog1.h"
#include "stdio.h"
int maxargs(A_stm stm);

int max(int x,int y)
{
	return x>y?x:y;
}

int countPrint(A_expList expList)
{
	if (expList->kind == A_pairExpList)
	{
		return 1+countPrint(expList->u.pair.tail);
	}
	else
		return 1;
}

int countAssign(A_exp exp)
{
	switch (exp->kind)
	{
	case A_opExp:
	{
		return max(countAssign(exp->u.op.left),
			countAssign(exp->u.op.right));
	}
	case A_eseqExp:
	{
		return max(maxargs(exp->u.eseq.stm),
			countAssign(exp->u.eseq.exp));
	}
	default:
		return 0;
	}
}


int maxargs(A_stm stm)
{
	//TODO: put your code here.

	switch (stm->kind)
	{
	case A_compoundStm:
	{
		return max(maxargs(stm->u.compound.stm1), 
			maxargs(stm->u.compound.stm2));
	}
	case A_assignStm:
	{
		return countAssign(stm->u.assign.exp);
		
	}
	case A_printStm:
	{
		return countPrint(stm->u.print.exps);
	}
	default:
		return 0;
	}
}




typedef struct table *Table_;
struct table {string id; int value; Table_ tail;};
Table_ Table(string id, int value,struct table *tail)
{
	Table_ t = malloc(sizeof(*t));
	t->id = id; 
	t->value = value;
	t->tail = tail;
	return t;
}

typedef struct intAndTable *IntAndTable_;
struct intAndTable {int i;Table_ t;};
IntAndTable_ IntAndTable(int i, Table_ t)
{
	IntAndTable_ temp = malloc(sizeof(*temp));
	temp->i = i;
	temp->t = t;
	return temp;
}

int lookup(Table_ t, string key)
{
	while (t)
	{
		if (t->id == key)
			return t->value;
		t = t->tail;
	}
	assert(TRUE);
	return 0;
}

Table_ update(Table_ t, string id, int newValue)
{
	return Table(id,newValue,t);
}

Table_ interpStm(A_stm s, Table_ t);
IntAndTable_ interpExp(A_exp e, Table_ t)
{
	IntAndTable_ temp = IntAndTable(0,t);
	switch (e->kind)
	{
	case A_idExp:
	{
		temp->i = lookup(t,e->u.id);
		return temp;
	}
	case A_numExp:
	{
		temp->i = e->u.num;
		return temp;
	}
	case A_opExp:
	{
		int i = interpExp(e->u.op.left,t)->i;
		int j = interpExp(e->u.op.right,t)->i;
		switch (e->u.op.oper)
		{
		case A_plus:
			temp->i = i+j;
			break;
		case A_minus:
			temp->i = i-j;
			break;
		case A_times:
			temp->i = i*j;
			break;
		case A_div:
			temp->i = i/j;
			break;
		}
		return temp;
	}
	case A_eseqExp:
	{
		temp->i = interpExp(e->u.eseq.exp,interpStm(e->u.eseq.stm,t))->i;
		return temp;
	}
	}
}

IntAndTable_ interpPrint(A_expList exps, Table_ t)
{
	IntAndTable_ temp = IntAndTable(0,t);
	while(exps->kind == A_pairExpList)
	{
		temp = interpExp(exps->u.pair.head,temp->t);
		printf("%d ",temp->i);
		exps = exps->u.pair.tail;
	}
	temp = interpExp(exps->u.last,temp->t);
	printf("%d\n", temp->i);
	return temp;
}

Table_ interpStm(A_stm s, Table_ t)
{
	switch (s->kind)
	{
	case A_compoundStm:
	{
		t = interpStm(s->u.compound.stm1,t);
		t = interpStm(s->u.compound.stm2,t);
		return t;
	}
	case A_assignStm:
	{
		t = update(t,s->u.assign.id,interpExp(s->u.assign.exp,t)->i);
		return t;

	}
	case A_printStm:
	{
		t = interpPrint(s->u.print.exps,t)->t;
		return t;
	}
	}
}

void interp(A_stm stm)
{
	//TODO: put your code here.
	interpStm(stm,NULL);
}

