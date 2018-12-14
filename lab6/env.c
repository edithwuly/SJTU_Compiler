#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "env.h"
#include "translate.h"

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Tr_access access, Ty_ty ty,int ro)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->u.var.ty = ty;
	entry->readonly = ro;
	entry->u.var.access = access;

	return entry;
}

E_enventry E_FunEntry(Tr_level level, Temp_label label, Ty_tyList formals, Ty_ty result)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->kind = E_funEntry;
	entry->u.fun.formals = formals;
	entry->u.fun.result = result;
	entry->u.fun.level = level;
	entry->u.fun.label = label;

	return entry;
}

S_table E_base_tenv(void)
{
	S_table table;
	S_symbol ty_int;
	S_symbol ty_string;

	table = S_empty();

	ty_int = S_Symbol("int");
	S_enter(table, ty_int, Ty_Int());

	ty_string = S_Symbol("string");
	S_enter(table, ty_string, Ty_String());

	return table;
}

S_table E_base_venv(void)
{
	S_table venv;

	Ty_ty result;
	Ty_tyList formals;
	
	Temp_label label = Temp_newlabel();
	Tr_level level;
	
	level = Tr_newLevel(Tr_outermost(), label, U_BoolList(1, NULL));;
	venv = S_empty();

	S_enter(venv,S_Symbol("flush"),E_FunEntry(level,label,NULL, Ty_Void()));
	
	result = Ty_Int();

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_Int();
	formals->tail = NULL;
	S_enter(venv,S_Symbol("exit"),E_FunEntry(level,label,formals, Ty_Void()));

	S_enter(venv,S_Symbol("not"),E_FunEntry(level,label,formals,result));

	result = Ty_String();
	
	S_enter(venv,S_Symbol("chr"),E_FunEntry(level,label,formals,result));

	S_enter(venv,S_Symbol("getchar"),E_FunEntry(level,label,NULL,result));

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = NULL;

	S_enter(venv,S_Symbol("print"),E_FunEntry(level,label,formals, Ty_Void()));

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_Int();
	formals->tail = NULL;

	S_enter(venv,S_Symbol("printi"),E_FunEntry(level,label,formals, Ty_Void()));

	result = Ty_Int();
	S_enter(venv,S_Symbol("ord"),E_FunEntry(level,label,formals,result));

	S_enter(venv,S_Symbol("size"),E_FunEntry(level,label,formals,result));

	result = Ty_String();
	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = checked_malloc(sizeof(*formals));
	formals->tail->head = Ty_String();
	S_enter(venv,S_Symbol("concat"),E_FunEntry(level,label,formals,result));

	formals = checked_malloc(sizeof(*formals));
	formals->head = Ty_String();
	formals->tail = checked_malloc(sizeof(*formals));
	formals->tail->head = Ty_Int();
	formals->tail->tail = checked_malloc(sizeof(*formals));
	formals->tail->tail->head = Ty_Int();
	S_enter(venv,S_Symbol("substring"),E_FunEntry(level,label,formals,result));

	return venv;
}
