#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/
const int F_wordSize = 4;

//varibales
struct F_frame_ {
	F_accessList formals;
	Temp_label name;
	int size;
};

struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

F_accessList F_AccessList(F_access head, F_accessList tail) {
	F_accessList temp = checked_malloc(sizeof(*temp));
	temp->head = head;
	temp->tail = tail;
	return temp;
}

static F_access InFrame(int offset) {
	F_access temp = checked_malloc(sizeof(*temp));
	temp->kind = inFrame;
	temp->u.offset = offset;
	return temp;
}

static F_access InReg(Temp_temp reg) {
	F_access temp = checked_malloc(sizeof(*temp));
	temp->kind = inReg;
	temp->u.reg = reg;
	return temp;
}

static F_accessList Formals(U_boolList formals, int offset) {
	if (formals)
		return F_AccessList(InFrame(offset), Formals(formals->tail ,offset + F_wordSize));

	return NULL;
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
	F_frame temp = checked_malloc(sizeof(*temp));
	temp->formals = Formals(formals, F_wordSize);
	temp->name = name;
	temp->size = 0;
	return temp;
}

Temp_label F_name(F_frame f) {
	return f->name;
}

F_accessList F_formals(F_frame f) {
	return f->formals;
}

F_access F_allocLocal(F_frame f, bool escape) {
	if (escape) 
	{
		f->size++;
		int offset = -(f->size * F_wordSize);
		return InFrame(offset);
	} 

	return InReg(Temp_newtemp());
}

Temp_temp F_FP(void) {
	return Temp_newtemp();
}

Temp_temp F_RV(void) {
	return Temp_newtemp();
}

T_exp F_Exp(F_access access, T_exp fp) {
	if (access->kind == inFrame) 
		return T_Mem(T_Binop(T_plus, fp, T_Const(access->u.offset)));
	return T_Temp(access->u.reg);
}

F_frag F_StringFrag(Temp_label label, string str) {  
	F_frag temp = checked_malloc(sizeof(*temp));
	temp->kind = F_stringFrag;
	temp->u.stringg.label = label;
	temp->u.stringg.str = str;
	return temp;
}                                                     
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {        
	F_frag temp = checked_malloc(sizeof(*temp));
	temp->kind = F_procFrag;
	temp->u.proc.body = body;
	temp->u.proc.frame = frame;
	return temp;
}                                                    
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
	F_fragList temp = checked_malloc(sizeof(*temp));
	temp->head = head;
	temp->tail = tail;
	return temp;                 
}      

T_exp F_externalCall(string s, T_expList args) {
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}                                               

