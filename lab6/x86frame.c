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
const int F_wordSize = 8;

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

static Temp_temp rax = NULL;
Temp_temp F_RAX(void) {
	if(rax == NULL)
	    rax = Temp_newtemp();

	return rax;
}

static Temp_temp rbx = NULL;
Temp_temp F_RBX(void) {
	if(rbx == NULL)
	    rbx = Temp_newtemp();

	return rbx;
}

static Temp_temp rcx = NULL;
Temp_temp F_RCX(void) {
	if(rcx == NULL)
	    rcx = Temp_newtemp();

	return rcx;
}

static Temp_temp rdx = NULL;
Temp_temp F_RDX(void) {
	if(rdx == NULL)
	    rdx = Temp_newtemp();

	return rdx;
}

static Temp_temp rsi = NULL;
Temp_temp F_RSI(void) {
	if(rsi == NULL)
	    rsi = Temp_newtemp();

	return rsi;
}

static Temp_temp rdi = NULL;
Temp_temp F_RDI(void) {
	if(rdi == NULL)
	    rdi = Temp_newtemp();

	return rdi;
}

static Temp_temp rsp = NULL;
Temp_temp F_RSP(void) {
	if(rsp == NULL)
	    rsp = Temp_newtemp();

	return rsp;
}

static Temp_temp rbp = NULL;
Temp_temp F_RBP(void) {
	if(rbp == NULL)
	    rbp = Temp_newtemp();

	return rbp;
}

static Temp_temp r8 = NULL;
Temp_temp F_R8(void) {
	if(r8 == NULL)
	    r8 = Temp_newtemp();

	return r8;
}

static Temp_temp r9 = NULL;
Temp_temp F_R9(void) {
	if(r9 == NULL)
	    r9 = Temp_newtemp();

	return r9;
}

static Temp_temp r10 = NULL;
Temp_temp F_R10(void) {
	if(r10 == NULL)
	    r10 = Temp_newtemp();

	return r10;
}

static Temp_temp r11 = NULL;
Temp_temp F_R11(void) {
	if(r11 == NULL)
	    r11 = Temp_newtemp();

	return r11;
}

static Temp_temp r12 = NULL;
Temp_temp F_R12(void) {
	if(r12 == NULL)
	    r12 = Temp_newtemp();

	return r12;
}

static Temp_temp r13 = NULL;
Temp_temp F_R13(void) {
	if(r13 == NULL)
	    r13 = Temp_newtemp();

	return r13;
}

static Temp_temp r14 = NULL;
Temp_temp F_R14(void) {
	if(r14 == NULL)
	    r14 = Temp_newtemp();

	return r14;
}

static Temp_temp r15 = NULL;
Temp_temp F_R15(void) {
	if(r15 == NULL)
	    r15 = Temp_newtemp();

	return r15;
}

Temp_temp F_FP(void) {
	return F_RBP();
}

Temp_temp F_RV(void) {
	return F_RAX();
}

static Temp_tempList callersaves = NULL;
Temp_tempList F_callersaves(void)
{
	if(callersaves == NULL) 
	    callersaves = Temp_TempList(F_RDI(),Temp_TempList(F_RSI(),Temp_TempList(F_RDX(), Temp_TempList(F_RCX(), Temp_TempList(F_R8(), Temp_TempList(F_R9(), NULL))))));

	return callersaves;
}

static Temp_tempList calleesaves = NULL;
Temp_tempList F_calleesaves(void)
{
	if(calleesaves == NULL)
	    calleesaves = Temp_TempList(F_RBX(),Temp_TempList(F_R12(), Temp_TempList(F_R13(), Temp_TempList(F_R14(), Temp_TempList(F_R15(), NULL)))));

	return calleesaves;
}

static Temp_tempList registers = NULL;
Temp_tempList F_registers(void)
{
	if(registers == NULL)
	    registers = Temp_TempList(F_RAX(),Temp_TempList(F_RBX(),Temp_TempList(F_RCX(),Temp_TempList(F_RDX(),Temp_TempList(F_RSI(),Temp_TempList(F_RDI(),
		Temp_TempList(F_R8(),Temp_TempList(F_R9(),Temp_TempList(F_R10(),Temp_TempList(F_R11(),Temp_TempList(F_R12(),Temp_TempList(F_R13(),Temp_TempList(F_R14(), 			Temp_TempList(F_R15(), NULL))))))))))))));

	return registers;
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

