#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"
#include "types.h"
#include "printtree.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;
struct Tr_accessList_{
	Tr_access head;
	Tr_accessList tail;	
};


typedef struct Tr_level_ *Tr_level;

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_level Tr_outermost(void);
Tr_level Tr_tigermain(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

typedef struct Tr_expList_ *Tr_expList;
struct Tr_expList_{
	Tr_exp head;
	Tr_expList tail;
};
Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail);

/* IR translation */
void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);
F_fragList Tr_getResult(void);

//transVar
Tr_exp Tr_simpleVar(Tr_access acc, Tr_level l);
Tr_exp Tr_fieldVar(Tr_exp base,  int cnt);
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp off);

//transExp
Tr_exp Tr_Nil();
Tr_exp Tr_Int(int i);
Tr_exp Tr_String(string str);
Tr_exp Tr_Call(Temp_label fname, Tr_expList params, Tr_level fl, Tr_level envl);
Tr_exp Tr_arithExp(A_oper op, Tr_exp left, Tr_exp right);
Tr_exp Tr_intCompExp(A_oper op, Tr_exp left, Tr_exp right);
Tr_exp Tr_strCompExp(A_oper op, Tr_exp left, Tr_exp right);
Tr_exp Tr_Record(Tr_expList list, int cnt);
Tr_exp Tr_Seq(Tr_expList list);
Tr_exp Tr_Assign(Tr_exp pos, Tr_exp val);
Tr_exp Tr_IfThenElse(Tr_exp test, Tr_exp then, Tr_exp elsee);
Tr_exp Tr_While(Tr_exp test, Tr_exp body, Temp_label done);
Tr_exp Tr_For(Tr_exp forvar, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done);
Tr_exp Tr_Break(Temp_label done);
Tr_exp Tr_Let(Tr_expList dec, Tr_exp body);
Tr_exp Tr_Array(Tr_exp size, Tr_exp initvar);

//transDec
Tr_exp Tr_varDec(Tr_access acc, Tr_exp init);

//print
void Tr_print(Tr_exp e);
#endif
