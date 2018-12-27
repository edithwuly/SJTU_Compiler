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

struct F_frame_ {
	Temp_label name;	
	F_accessList formals;
	F_accessList locals;
	int size;
};

struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

static F_access InFrame(int offset){
	F_access ac = checked_malloc(sizeof(*ac));

	ac->kind = inFrame;
	ac->u.offset = offset;
	return ac;
}   

static F_access InReg(Temp_temp reg){
	F_access ac = checked_malloc(sizeof(*ac));

	ac->kind = inReg;
	ac->u.reg = reg;
	return ac;
}

F_accessList F_AccessList(F_access head, F_accessList tail){
	F_accessList l = checked_malloc(sizeof(*l));

	l->head = head;
	l->tail = tail;
	return l;
}

F_accessList makeFormals(F_frame f, U_boolList formals){
	if(!formals)
	    return NULL;

	bool esc = formals->head;
	F_access ac = F_allocLocal(f, esc);
	
	return F_AccessList(ac, makeFormals(f, formals->tail));
}

F_frame F_newFrame(Temp_label name, U_boolList formals){
	F_frame f = checked_malloc(sizeof(*f));
	f->size = 0;
	f->name = name;
	f->formals = makeFormals(f, formals);
	f->locals = NULL;

	return f;
}

F_access F_allocLocal(F_frame f, bool escape){
	int size = f->size;

	F_access ac;
	if(escape)
	{
	    ac = InFrame(-(size+1) * F_wordSize);
	    f->size++;
	}
	else
	    ac = InReg(Temp_newtemp());
	
	f->locals = F_AccessList(ac, f->locals);

	return ac;
}

Temp_label F_name(F_frame f){
	return f->name;
}

F_accessList F_formals(F_frame f){
	return f->formals;
}

int F_size(F_frame f){
	return f->size;
}


int F_getFrameOff(F_access acc){
	return acc->u.offset;
}

static Temp_temp rax = NULL;
Temp_temp F_RAX(void) {
	if(rax == NULL)
	{
	    rax = Temp_newtemp();
	    Temp_enter(F_tempMap, rax, "%rax");
	}

	return rax;
}

static Temp_temp rbx = NULL;
Temp_temp F_RBX(void) {
	if(rbx == NULL)
	{
	    rbx = Temp_newtemp();
	    Temp_enter(F_tempMap, rbx, "%rbx");
	}

	return rbx;
}

static Temp_temp rcx = NULL;
Temp_temp F_RCX(void) {
	if(rcx == NULL)
	{
	    rcx = Temp_newtemp();
	    Temp_enter(F_tempMap, rcx, "%rcx");
	}

	return rcx;
}

static Temp_temp rdx = NULL;
Temp_temp F_RDX(void) {
	if(rdx == NULL)
	{
	    rdx = Temp_newtemp();
	    Temp_enter(F_tempMap, rdx, "%rdx");
	}

	return rdx;
}

static Temp_temp rsi = NULL;
Temp_temp F_RSI(void) {
	if(rsi == NULL)
	{
	    rsi = Temp_newtemp();
	    Temp_enter(F_tempMap, rsi, "%rsi");	
	}

	return rsi;
}

static Temp_temp rdi = NULL;
Temp_temp F_RDI(void) {
	if(rdi == NULL)
	{
	    rdi = Temp_newtemp();
	    Temp_enter(F_tempMap, rdi, "%rdi");
	}

	return rdi;
}

static Temp_temp rsp = NULL;
Temp_temp F_RSP(void) {
	if(rsp == NULL)
	{
	    rsp = Temp_newtemp();
	    Temp_enter(F_tempMap, rsp, "%rsp");
	}

	return rsp;
}

static Temp_temp rbp = NULL;
Temp_temp F_RBP(void) {
	if(rbp == NULL)
	{
	    rbp = Temp_newtemp();
	    Temp_enter(F_tempMap, rbp, "%rbp");
	}

	return rbp;
}

static Temp_temp r8 = NULL;
Temp_temp F_R8(void) {
	if(r8 == NULL)
	{
	    r8 = Temp_newtemp();
	    Temp_enter(F_tempMap, r8, "%r8");
	}

	return r8;
}

static Temp_temp r9 = NULL;
Temp_temp F_R9(void) {
	if(r9 == NULL)
	{
	    r9 = Temp_newtemp();
	    Temp_enter(F_tempMap, r9, "%r9");
	}

	return r9;
}

static Temp_temp r10 = NULL;
Temp_temp F_R10(void) {
	if(r10 == NULL)
	{
	    r10 = Temp_newtemp();
	    Temp_enter(F_tempMap, r10, "%r10");
	}

	return r10;
}

static Temp_temp r11 = NULL;
Temp_temp F_R11(void) {
	if(r11 == NULL)
	{
	    r11 = Temp_newtemp();
	    Temp_enter(F_tempMap, r11, "%r11");
	}

	return r11;
}

static Temp_temp r12 = NULL;
Temp_temp F_R12(void) {
	if(r12 == NULL)
	{
	    r12 = Temp_newtemp();
	    Temp_enter(F_tempMap, r12, "%r12");
	}

	return r12;
}

static Temp_temp r13 = NULL;
Temp_temp F_R13(void) {
	if(r13 == NULL)
	{
	    r13 = Temp_newtemp();
	    Temp_enter(F_tempMap, r13, "%r13");
	}

	return r13;
}

static Temp_temp r14 = NULL;
Temp_temp F_R14(void) {
	if(r14 == NULL)
	{
	    r14 = Temp_newtemp();
	    Temp_enter(F_tempMap, r14, "%r14");
	}

	return r14;
}

static Temp_temp r15 = NULL;
Temp_temp F_R15(void) {
	if(r15 == NULL)
	{
	    r15 = Temp_newtemp();
	    Temp_enter(F_tempMap, r15, "%r15");
	}

	return r15;
}

static Temp_temp fp  = NULL;
Temp_temp F_FP(void){
	if(!fp)
	{
	    fp = Temp_newtemp();
	    Temp_enter(F_tempMap, fp, "fp");
	}
	return fp;
}

Temp_temp F_SP(void){
	return F_RSP();
}

Temp_temp F_RV(void){
	return F_RAX();
}

static Temp_tempList args = NULL;
Temp_tempList F_Args(){
	if(!args)
	    args = Temp_TempList(F_RDI(),Temp_TempList(F_RSI(),Temp_TempList(F_RDX(),Temp_TempList(F_RCX(),Temp_TempList(F_R8(),Temp_TempList(F_R9(),NULL))))));
	
	return args;
}

static Temp_tempList callerSave = NULL;
Temp_tempList F_callerSave(){
	if(!callerSave)
	    callerSave = Temp_catList(F_Args(), Temp_TempList(F_R10(), Temp_TempList(F_R11(), NULL)));
	
	return callerSave;
}

static Temp_tempList calleeSave = NULL;
Temp_tempList F_calleeSave(){	
	if(!calleeSave)
	    calleeSave = Temp_TempList(F_R12(),Temp_TempList(F_R13(),Temp_TempList(F_R14(),Temp_TempList(F_R15(),Temp_TempList(F_RBX(),Temp_TempList(F_RBP(), NULL))))));
	
	return calleeSave;
}

static Temp_tempList regs = NULL;
Temp_tempList F_register(){
	if(!regs)
	{
	    regs = Temp_TempList(F_RSP(),Temp_TempList(F_RAX(),F_calleeSave()));
	    regs = Temp_catList(regs, F_callerSave());
	}
	return regs;											
}

T_exp F_exp(F_access acc, T_exp framePtr){
	if(acc->kind == inFrame)
	    return T_Mem(T_Binop(T_plus, T_Const(acc->u.offset), framePtr));

	return T_Temp(acc->u.reg);
	
}

T_exp F_externalCall(string s, T_expList args){
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}


/* fragment */
F_frag F_StringFrag(Temp_label label, string str) { 
	F_frag f = checked_malloc(sizeof(*f));
	f->kind = F_stringFrag;
	f->u.stringg.label = label;
	f->u.stringg.str = str;

	return f;                                      
}                                                     
                                                      
F_frag F_ProcFrag(T_stm body, F_frame frame) {        
	F_frag f = checked_malloc(sizeof(*f));
	f->kind = F_procFrag;
	f->u.proc.body = body;
	f->u.proc.frame = frame;

	return f;                                     
}                                                     
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
	F_fragList l = checked_malloc(sizeof(*l));
	l->head = head;
	l->tail = tail;
	return l;                                      
}                                                     

T_stm F_procEntryExit1(F_frame f, T_stm stm){
	T_stm view = NULL;
	int cnt = 0;
	T_exp fp = T_Temp(F_FP());
	for(F_accessList l=f->formals;l;l=l->tail,cnt++)
	{
	    switch(cnt)
	    {
		case 0:
		    view = T_Move(F_exp(l->head, T_Temp(F_FP())),T_Temp(F_RDI()));
		    break;
		case 1:
		    view = T_Seq(T_Move(F_exp(l->head, T_Temp(F_FP())),T_Temp(F_RSI())),view);
		    break;
		case 2:
		    view = T_Seq(T_Move(F_exp(l->head, T_Temp(F_FP())),T_Temp(F_RDX())),view);
		    break;
		case 3:
		    view = T_Seq(T_Move(F_exp(l->head, T_Temp(F_FP())),T_Temp(F_RCX())),view);
		    break;
		case 4:
		    view = T_Seq(T_Move(F_exp(l->head, T_Temp(F_FP())),T_Temp(F_R8())),view);
		    break;
		case 5:
		    view = T_Seq(T_Move(F_exp(l->head, T_Temp(F_FP())),T_Temp(F_R9())),view);
		    break;
		default:		    
		    view = T_Seq(T_Move(F_exp(l->head, fp),T_Mem(T_Binop(T_plus, T_Const((cnt-5)*F_wordSize),fp))),view);
	    }
	}

	F_accessList l = NULL;
	F_accessList last = NULL;
	T_stm save = NULL;
	for(Temp_tempList tl = F_calleeSave();tl;tl=tl->tail)
	{
	    F_access acc = F_allocLocal(f,FALSE);
	    if(!last)
	    {
		last = F_AccessList(acc, NULL);
		l = last;
	    }
	    else
	    {
		last->tail = F_AccessList(acc, NULL);
		last = last->tail;
	    }
	    T_exp pos = F_exp(acc, fp);
	    if(save)
		save = T_Seq(T_Move(pos, T_Temp(tl->head)), save);
	    else
		save = T_Move(pos, T_Temp(tl->head));
	}

	T_stm restore = NULL;
	for(Temp_tempList tl = F_calleeSave();tl;tl=tl->tail, l=l->tail)
	{
	    T_exp pos = F_exp(l->head, fp);
	    if(restore)
		restore = T_Seq(T_Move(T_Temp(tl->head),pos), restore);	
	    else
		restore = T_Move(T_Temp(tl->head), pos);
		
	}

	if(!view)
	    return T_Seq(save,T_Seq(stm, restore));
	
	return T_Seq(save,T_Seq(view, T_Seq(stm, restore)));
}

AS_instrList F_procEntryExit2(AS_instrList body){
	static Temp_tempList returnSink = NULL ;
	if (!returnSink)  
		returnSink = Temp_TempList(F_SP(), F_calleeSave());
    return AS_splice(body,AS_InstrList(AS_Oper("ret", NULL, returnSink, NULL), NULL));

}

AS_proc F_procEntryExit3(F_frame frame, AS_instrList body){
	int size = frame->size;
	string fn =  S_name(F_name(frame));
	char target[100];
	char length[20];
	sprintf(target, "%s_framesize", fn);
	sprintf(length, "%d", F_wordSize*size);
	AS_rewriteFrameSize(body, target, length);

	return AS_Proc("", body, "");
}

