#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "env.h"

/*Lab4: Your implementation of lab4*/

E_enventry E_VarEntry(Ty_ty ty,int ro)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->u.var.ty = ty;
	entry->readonly = ro;

	return entry;
}

E_enventry E_FunEntry(Ty_tyList formals, Ty_ty result)
{
	E_enventry entry = checked_malloc(sizeof(*entry));
	entry->kind = E_funEntry;
	entry->u.fun.formals = formals;
	entry->u.fun.result = result;

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
	S_table table;

	table = S_empty();

	return table;
}
