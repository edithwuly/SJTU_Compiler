#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"
#include "escape.h"
#include "printtree.h"

/*Lab5: Your implementation of lab5.*/

struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params) {
	if (!params) 
	    return NULL;

	Ty_ty type = S_look(tenv, params->head->typ);
	return Ty_TyList(S_look(tenv, params->head->typ), makeFormalTyList(tenv, params->tail));
}

U_boolList makeFormalEscList(A_fieldList params) {
	if (!params) 
	    return NULL;

    	return U_BoolList(params->head->escape, makeFormalEscList(params->tail));
}

Ty_ty checkTy(Ty_ty ty){
	if (ty->kind == Ty_name) 
            return ty->u.name.ty;

        return ty;
}

Ty_fieldList makeFields(S_table tenv, A_fieldList record, bool recursive){
	if (!record)
	    return NULL;

	Ty_ty ty = S_look(tenv, record->head->typ);
	Ty_field field;
	if(ty && (ty->kind == Ty_string || ty->kind == Ty_int))
	    field = Ty_Field(record->head->name, ty);			
	
	else if(recursive)
	    field = Ty_Field(record->head->name, NULL);
	
	else if(ty && ty->kind == Ty_name)
	    field = Ty_Field(record->head->name, ty);
	
	else
	{
	    EM_error(record->head->pos, "undefined type %s", S_name(record->head->typ));
	    return NULL;
	}
	
	return Ty_FieldList(field, makeFields(tenv, record->tail, recursive));				
}

Ty_ty actual_ty(Ty_ty ty){
	while (ty->kind==Ty_name)
	    ty = ty->u.name.ty;
	
	return ty;
}

bool isLoopVar(S_table venv, A_var v) {
	switch(v->kind) 
	{
	    case A_simpleVar: 
	    {
		E_enventry x = S_look(venv, v->u.simple);
		if (x->readonly) 
		    return TRUE;
		return FALSE;
	    }
	   case A_fieldVar:
		return isLoopVar(venv, v->u.field.var);
	   case A_subscriptVar:
		return isLoopVar(venv, v->u.subscript.var);
	}
}



/* core functions */
F_fragList SEM_transProg(A_exp exp){
	//TODO LAB5: do not forget to add the main frame
	S_table venv = E_base_venv();
	S_table tenv = E_base_tenv();

	Tr_level level = Tr_tigermain();
	struct expty body = transExp(venv, tenv, exp, level, Temp_newlabel());

	Tr_procEntryExit(level, body.exp, NULL);
	
	return Tr_getResult(); 
}


Ty_ty transTy(S_table tenv, A_ty a, bool recursive){
	switch(a->kind)
	{
	    case A_nameTy:
	    {
		Ty_ty ty = S_look(tenv, get_ty_name(a));
		if(ty && (ty->kind == Ty_string || ty->kind == Ty_int))
		    return ty;
			
		if(recursive)
		    return NULL;
			
		if(ty && ty->kind == Ty_name)
		    return ty;
			
		EM_error(a->pos, "undefined type %s", S_name(get_ty_name(a)));
		return Ty_Int();
	    }
	    case A_recordTy:
	    {
		A_fieldList record = get_ty_record(a);
		Ty_fieldList fields = makeFields(tenv, record, recursive);
		if(fields)
		    return Ty_Record(fields);
			
		return Ty_Int();
			
	    }
	    case A_arrayTy:
	    {
		S_symbol array = get_ty_array(a);
		Ty_ty ty = S_look(tenv, array);

		if(ty &&(ty->kind == Ty_string || ty->kind == Ty_int ))
		    return Ty_Array(ty);
			
		if(recursive)
		    return NULL;
			
		if(ty && ty->kind == Ty_name)
		    return Ty_Array(ty);
			
		EM_error(a->pos, "undefined type %s", S_name(array));
		return Ty_Int();

	    }
	}
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level level, Temp_label label){
	switch(d->kind)
	{
	    case A_typeDec:
	    {
		for(A_nametyList types= get_typedec_list(d);types;types=types->tail)
		{
		    if(S_look(tenv, types->head->name))
		    {
			EM_error(d->pos, "two types have the same name");
			return Tr_Nil(); 
		    }
		    S_enter(tenv,types->head->name,Ty_Name(types->head->name, transTy(tenv,types->head->ty, TRUE)));
		}

		for(A_nametyList types= get_typedec_list(d);types;types=types->tail)
		    S_enter(tenv,types->head->name,Ty_Name(types->head->name, transTy(tenv,types->head->ty, FALSE)));
			

		for(A_nametyList types= get_typedec_list(d);types;types=types->tail)
		    if(!checkTy(S_look(tenv, types->head->name)))
		    {
			EM_error(d->pos, "illegal type cycle");
			return Tr_Nil(); 
		    }

		return Tr_Nil(); 
	    }
	    case A_varDec: 
	    {
		S_symbol var = get_vardec_var(d);
		S_symbol typ =  get_vardec_typ(d);
		A_exp init = get_vardec_init(d);
		bool esc = d->u.var.escape;
		struct expty exp = transExp(venv, tenv, init, level, label);

		if (typ) 
		{
		    Ty_ty ty = S_look(tenv, typ);
		    if (!ty)
		    {
			EM_error(d->u.var.init->pos, "type not exist %s", S_name(d->u.var.typ));
			return Tr_Nil();
		    }
		    if (actual_ty(ty) != actual_ty(exp.ty) && !(ty->kind == Ty_record && exp.ty->kind == Ty_nil))
		    {
			EM_error(d->u.var.init->pos, "type mismatch");
			return Tr_Nil();
		    }
		}
		else if (get_expty_kind(exp) == Ty_nil) 
		{
		    EM_error(d->u.var.init->pos, "init should not be nil without type specified");
		    return Tr_Nil();
		}

		Tr_access acc = Tr_allocLocal(level, esc);
		S_enter(venv, var, E_VarEntry(acc, actual_ty(exp.ty),0));
		return Tr_varDec(acc, exp.exp);
	    }		
	    case A_functionDec:
	    {

		for(A_fundecList funcs=get_funcdec_list(d); funcs; funcs=funcs->tail)
		{
		    A_fundec func = funcs->head;
		    A_fieldList params = func->params;  
		    Tr_level newlevel = Tr_newLevel(level, func->name, makeFormalEscList(params));
		    Ty_tyList formals = makeFormalTyList(tenv, params);

		    if(func->result)
			S_enter(venv, func->name, E_FunEntry(newlevel,func->name,formals, S_look(tenv, func->result)));
		    else
			S_enter(venv, func->name, E_FunEntry(newlevel,func->name,formals, Ty_Void()));
				
		    S_beginScope(venv);

		    for(Tr_accessList acc=Tr_formals(newlevel)->tail; params; params=params->tail, acc=acc->tail)
			S_enter(venv, params->head->name, E_VarEntry(acc->head,S_look(tenv, params->head->typ), 0));
			
		    struct expty result = transExp(venv, tenv, func->body, newlevel, func->name);
				
		    S_endScope(venv);

		    if(func->result && actual_ty(S_look(tenv, func->result))->kind == actual_ty(result.ty)->kind || !func->result && actual_ty(result.ty)->kind == Ty_void)
			Tr_procEntryExit(newlevel, result.exp, Tr_formals(newlevel));

		    else
		    {
			EM_error(d->pos, "procedure returns value");
			return Tr_Nil(); 
		    }
		}			
		return Tr_Nil();
	    }
	}
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level l, Temp_label label){
	switch(v->kind){
	    case A_simpleVar:
            {
                E_enventry x = S_look(venv, get_simplevar_sym(v));
                if (x && x->kind == E_varEntry) 
                    return expTy(Tr_simpleVar(x->u.var.access, l),actual_ty(get_varentry_type(x))); 
		else 
		{
                    EM_error(v->pos,"undefined variable %s",S_name(v->u.simple));
                    return expTy(Tr_Nil(),Ty_Int());
                }
            }
	    case A_fieldVar:
            {
                struct expty var = transVar(venv, tenv, v->u.field.var, l, label);
                if (!(var.ty->kind == Ty_record)) 
		{
                    EM_error(v->u.field.var->pos, "not a record type");
                    return expTy(Tr_Nil(),Ty_Int());
                } 
		else 
		{
		    int n = 0;
                    for (Ty_fieldList field = var.ty->u.record; field; field = field->tail) 
		    {
                        if (field->head->name == v->u.field.sym) 
                            return expTy(Tr_fieldVar(var.exp, n), field->head->ty);
			n++;
                    }
                    EM_error(v->u.field.var->pos, "field %s doesn't exist", S_name(v->u.field.sym));
                    return expTy(Tr_Nil(),Ty_Int());
                }
            }
	    case A_subscriptVar: 
	    {

		struct expty var = transVar(venv, tenv, v->u.subscript.var, l, label);
		struct expty index = transExp(venv, tenv, v->u.subscript.exp, l, label);
		if (var.ty->kind != Ty_array) 
		{
		    EM_error(v->pos, "array type required");
		    return expTy(Tr_Nil(), Ty_Int());
		}
		if (index.ty->kind != Ty_int) 
		{
		    EM_error(v->pos, "index type is not int");
		    return expTy(Tr_Nil(), Ty_Int());
		}
		return expTy(Tr_subscriptVar(var.exp, index.exp), var.ty->u.array);
	    }
	}
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level, Temp_label label){
	switch(a->kind)
	{
	    case A_varExp:
                return transVar(venv, tenv, a->u.var, level, label);
            case A_nilExp:
            	return expTy(Tr_Nil(),Ty_Nil());
            case A_intExp:
            	return expTy(Tr_Int(a->u.intt),Ty_Int());
            case A_stringExp:
            	return expTy(Tr_String(a->u.stringg),Ty_String());
	    case A_callExp:
	    {
		S_symbol func = get_callexp_func(a); 
		A_expList args = get_callexp_args(a);
			
		E_enventry x = S_look(venv, func);
		if(x && x->kind == E_funEntry)
		{
		    Ty_tyList formals = get_func_tylist(x); 
		    Ty_ty result = get_func_res(x);
		    A_expList exps;
		    Ty_tyList tys;
		    Tr_expList ls = NULL;
		    for(exps=args,tys=formals;exps&&tys;exps=exps->tail,tys=tys->tail)
		    {
			A_exp param = exps->head;
			Ty_ty ty = tys->head;
					
			struct expty pp = transExp(venv, tenv, param, level, label);
					
			if(actual_ty(pp.ty)->kind != actual_ty(ty)->kind)
			{
			    EM_error(param->pos, "para type mismatch");
			    return expTy(Tr_Nil(), Ty_Int());
			}
			ls = Tr_ExpList(pp.exp, ls);
		    }
		    if(exps != NULL)
		    {
			EM_error(a->pos, "too many params in function %s", S_name(func));
			return expTy(Tr_Nil(), Ty_Int());
		    }
		    if(tys != NULL)
		    {
			EM_error(a->pos, "too less params in function %s", S_name(func));
			return expTy(Tr_Nil(), Ty_Int());
		    }
		    Temp_label funLabel = get_func_label(x);
		    Tr_level funLevel = get_func_level(x);
		    return expTy(Tr_Call(funLabel, ls, funLevel, level), result);
		}
		else
		{
			EM_error(a->pos, "undefined function %s", S_name(func));
			return expTy(Tr_Nil(), Ty_Int());
		}
	    }
	    case A_opExp:
	    {
		struct expty left = transExp(venv, tenv, get_opexp_left(a), level, label);
		struct expty right = transExp(venv, tenv, get_opexp_right(a), level, label);

		switch(get_opexp_oper(a))
		{
		    case A_plusOp:case A_minusOp:case A_timesOp:case A_divideOp:
		    {
			if(actual_ty(left.ty)->kind != Ty_int)
			{
			    EM_error(get_opexp_leftpos(a), "integer required");
			    return expTy(Tr_Nil(), Ty_Int());
			}
			if(actual_ty(right.ty)->kind != Ty_int)
			{
			    EM_error(get_opexp_rightpos(a), "integer required");
			    return expTy(Tr_Nil(), Ty_Int());
			}					
			return expTy(Tr_arithExp(get_opexp_oper(a),left.exp,right.exp), Ty_Int());
		    }
		    default:
		    {
			if(actual_ty(left.ty)->kind == Ty_string)   
			    return expTy(Tr_strCompExp(get_opexp_oper(a),left.exp,right.exp), Ty_Int());
			else
			    return expTy(Tr_intCompExp(get_opexp_oper(a),left.exp,right.exp), Ty_Int()); 					
			EM_error(get_opexp_leftpos(a), "same type required");
			return expTy(Tr_Nil(), Ty_Int());
		    }
		}
	    }
	    case A_recordExp: 
	    {
		Ty_ty type = S_look(tenv, get_recordexp_typ(a));
			
		if(actual_ty(type) && actual_ty(type)->kind == Ty_record)
		{
		    Ty_fieldList record = actual_ty(type)->u.record;
		    A_efieldList fields = get_recordexp_fields(a);
		    Tr_expList list = NULL;
		    int count = 0;
		    for(; record && fields; record=record->tail,fields=fields->tail,count++)
			list = Tr_ExpList(transExp(venv, tenv, fields->head->exp, level, label).exp, list);

		    return expTy(Tr_Record(list, count), type);
		}
		else
		{
		    EM_error(a->pos, "undefined type %s", S_name(get_recordexp_typ(a)));
		    return expTy(Tr_Nil(), Ty_Int());
		}
	    }
	    case A_seqExp:
	    {
		struct expty ety;

		Tr_expList list = NULL;
		for(A_expList seq = get_seqexp_seq(a); seq; seq=seq->tail)
		{
		    ety = transExp(venv, tenv, seq->head, level, label);
		    list = Tr_ExpList(ety.exp, list);
		}
		return expTy(Tr_Seq(list), ety.ty);
	    }
	    case A_assignExp:
            {
                struct expty var = transVar(venv, tenv, get_assexp_var(a), level, label);
                struct expty exp = transExp(venv, tenv, get_assexp_exp(a), level, label);
		if (isLoopVar(venv, a->u.assign.var))
		    EM_error(a->pos, "loop variable can't be assigned");

		if (actual_ty(var.ty) != actual_ty(exp.ty)) 
		    EM_error(a->pos, "unmatched assign exp");
                return expTy(Tr_Assign(var.exp, exp.exp),Ty_Void());
            }
	    case A_ifExp:
	    {
		struct expty test = transExp(venv, tenv, get_ifexp_test(a), level, label);
		struct expty then = transExp(venv, tenv, get_ifexp_then(a), level, label);
		struct expty elsee = transExp(venv, tenv, get_ifexp_else(a), level, label);

		if(actual_ty(elsee.ty)->kind == Ty_nil)
		    return expTy(Tr_IfThenElse(test.exp,then.exp,elsee.exp), then.ty);
		else if(actual_ty(then.ty)->kind == actual_ty(elsee.ty)->kind)
		    return expTy(Tr_IfThenElse(test.exp,then.exp,elsee.exp), elsee.ty);
		else
		{
		    EM_error(a->pos, "then exp and else exp type mismatch");
		    return expTy(Tr_Nil(), Ty_Int());
		}
	    }
	    case A_whileExp:
            {
		Temp_label done = Temp_newlabel();
                struct expty test = transExp(venv, tenv,get_whileexp_test(a), level, label);
                struct expty body = transExp(venv, tenv,get_whileexp_body(a), level, done);
                if (body.ty->kind != Ty_void)
                    EM_error(a->u.whilee.body->pos, "while body must produce no value");
                return expTy(Tr_While(test.exp, body.exp, done),Ty_Void());
            }
	    case A_forExp:
            {
		Temp_label done = Temp_newlabel();
                struct expty lo = transExp(venv, tenv, get_forexp_lo(a), level, label);
                struct expty hi = transExp(venv, tenv, get_forexp_hi(a), level, label);
                if (lo.ty->kind != Ty_int)
                    EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
                if (hi.ty->kind != Ty_int) 
                    EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");

                S_beginScope(venv);
		Tr_access access = Tr_allocLocal(level, a->u.forr.escape);
                S_enter(venv,a->u.forr.var, E_VarEntry(access, Ty_Int(), 1));
                struct expty body = transExp(venv, tenv, get_forexp_body(a), level, done);
                if (get_expty_kind(body) != Ty_void) 
                    EM_error(a->u.forr.body->pos, "while body must produce no value");
                S_endScope(venv);
                return expTy(Tr_For(Tr_simpleVar(access, level), lo.exp, hi.exp, body.exp, done), Ty_Void());
            }
	    case A_breakExp:
		return expTy(Tr_Break(label), Ty_Void());
	    case A_letExp:
	    {
		Tr_expList li = NULL;
		S_beginScope(tenv); 
		S_beginScope(venv);
		for(A_decList decs=get_letexp_decs(a); decs; decs=decs->tail)
		    li = Tr_ExpList(transDec(venv, tenv, decs->head, level, label), li);

		struct expty body = transExp(venv, tenv, get_letexp_body(a), level, label);
		S_endScope(venv); 
		S_endScope(tenv);

		return expTy(Tr_Let(li, body.exp),body.ty);

	    }
	    case A_arrayExp:
	    { 
		Ty_ty type = S_look(tenv, get_arrayexp_typ(a));
		if(actual_ty(type) && actual_ty(type)->kind == Ty_array)
		{
		    struct expty size = transExp(venv, tenv, get_arrayexp_size(a), level, label);
		    struct expty init = transExp(venv, tenv, get_arrayexp_init(a), level, label);
		    if(size.ty->kind != Ty_int)
		    {
			EM_error(a->pos, "array size type not integer");
			return expTy(Tr_Nil(), Ty_Int());
		    }

		    if(actual_ty(init.ty) != actual_ty(type)->u.array)
		    {
			EM_error(a->pos, "type mismatch");
			return expTy(Tr_Nil(), Ty_Int());
		    }

		    return expTy(Tr_Array(size.exp, init.exp), type);
		}
		else
		{
		    EM_error(a->pos, "undefined type %s", S_name(get_arrayexp_typ(a)));
		    return expTy(Tr_Nil(), Ty_Int());
		}
	    }
	}
}
