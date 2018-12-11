#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"

/*Lab4: Your implementation of lab4*/


typedef void* Tr_exp;
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


void SEM_transProg(A_exp exp) 
{
	transExp(E_base_venv(), E_base_tenv(), exp);
}

Ty_ty actual_ty(Ty_ty ty) 
{
    	if (ty->kind == Ty_name) 
            return ty->u.name.ty;
    	else 
            return ty;
}

Ty_fieldList tyFieldList(A_pos pos, S_table tenv, A_fieldList fields) 
{
	Ty_ty type = S_look(tenv, fields->head->typ);
	if (!type) 
	{
	    EM_error(pos, "undefined type %s", S_name(fields->head->typ));
	    type = Ty_Int();
	}
	Ty_field field = Ty_Field(fields->head->name, type);

	if (fields->tail == NULL) 
	    return Ty_FieldList(field, NULL);
	else
	    return Ty_FieldList(field, tyFieldList(pos, tenv, fields->tail));
}

Ty_tyList makeFormalTyList(A_pos pos, S_table tenv, A_fieldList params) {
	if (params == NULL) 
		return NULL;

	Ty_ty type = S_look(tenv, params->head->typ);
	return Ty_TyList(type, makeFormalTyList(pos, tenv, params->tail));
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

void transDec(S_table venv, S_table tenv, A_dec d) 
{
	switch (d->kind) 
	{
	    case A_varDec: 
	    {
		S_symbol var = get_vardec_var(d);
		S_symbol typ =  get_vardec_typ(d);
		A_exp init = get_vardec_init(d);
		struct expty exp = transExp(venv, tenv, init);

		if (typ) 
		{
		    Ty_ty ty = S_look(tenv, typ);
		    if (!ty)
			EM_error(d->u.var.init->pos, "type not exist %s", S_name(d->u.var.typ));
		    if (actual_ty(ty) != actual_ty(exp.ty))
			 EM_error(d->u.var.init->pos, "type mismatch");
		}
		if (actual_ty(exp.ty)->kind == Ty_nil) 
		    EM_error(d->u.var.init->pos, "init should not be nil without type specified");

		S_enter(venv, var, E_VarEntry(actual_ty(exp.ty),0));
		break;
	    }
	    case A_functionDec:
            {
                Ty_ty resultTy;
                struct expty exp;
                for (A_fundecList fun = get_funcdec_list(d);fun;fun = fun->tail) 
		{
		    if (S_look(venv, fun->head->name)) 
                        EM_error(d->pos, "two functions have the same name");
                    if (fun->head->result)
                        resultTy = S_look(tenv, fun->head->result);
                    else
                        resultTy = Ty_Void();
                    Ty_tyList formalTys = makeFormalTyList(d->pos, tenv, fun->head->params);
		    S_enter(venv, fun->head->name, E_FunEntry(formalTys, resultTy));
                }
                for (A_fundecList fun = get_funcdec_list(d);fun;fun = fun->tail) 
		{
                    S_beginScope(venv);
                    E_enventry f = S_look(venv, fun->head->name);
                    Ty_tyList t = f->u.fun.formals;
                    resultTy = f->u.fun.result;
                    for (A_fieldList l = fun->head->params;l;l = l->tail,t = t->tail) 
		    {
                        S_enter(venv, l->head->name, E_VarEntry(t->head,0));
                    }
                    exp = transExp(venv, tenv, fun->head->body);
		    if (actual_ty(exp.ty) != actual_ty(resultTy)) 
		    {
                        if (resultTy->kind == Ty_void)
                            EM_error(fun->head->body->pos, "procedure returns value");
			else
                            EM_error(fun->head->body->pos, "type mismatch");
                    }
                    S_endScope(venv);
                }
                break;
            }
	    case A_typeDec:
	    {
		for (A_nametyList nametys = get_typedec_list(d);nametys;nametys = nametys->tail) 
		{
		    S_symbol name = nametys->head->name;
		    if (S_look(tenv, name))
			EM_error(d->pos, "two types have the same name");
                    S_enter(tenv, name, Ty_Name(name, NULL));
            	}

		int count = 0;
                for (A_nametyList list = get_typedec_list(d);list;list = list->tail) 
		{
		    Ty_ty ty = S_look(tenv, list->head->name);
                    switch(list->head->ty->kind) 
		    {	
                        case A_nameTy:
                        {                      
                            ty->u.name.sym = get_ty_name(list->head->ty);
                            count++;
                            break;
                        }
                        case A_recordTy:
                        {
                            ty->kind = Ty_record;
                            ty->u.record = tyFieldList(d->pos, tenv, get_ty_record(list->head->ty));
                            break;
                        }
                        case A_arrayTy:
                        {
                            ty->kind = Ty_array;
                            ty->u.array = S_look(tenv, get_ty_array(list->head->ty));
                            break;
                        }
                    }
                }
                while (count > 0) 
		{
                    for (A_nametyList list = get_typedec_list(d);list;list = list->tail) 
		    {
                        if (list->head->ty->kind == A_nameTy) 
			{
                            Ty_ty ty = S_look(tenv, list->head->name);
                            if (!ty->u.name.ty) 
			    {
                                Ty_ty temp = S_look(tenv, ty->u.name.sym);
                                if (temp->kind == Ty_name) 
				{
                                    if (temp->u.name.ty)
                                        ty->u.name.ty = temp->u.name.ty;
				    else 
                                        count--;
                                } 
				else 
                                    ty->u.name.ty = temp;
                            }
                        }
                    }
                    if (!count)
                        EM_error(d->pos, "illegal type cycle");
                    break;
                }
	        
	    }
	}
}

struct expty transVar(S_table venv, S_table tenv, A_var v)
{
    	switch(v->kind) 
	{
            case A_simpleVar:
            {
                E_enventry x = S_look(venv, get_simplevar_sym(v));
                if (x && x->kind == E_varEntry) 
                    return expTy(NULL,actual_ty(get_varentry_type(x))); 
		else 
		{
                    EM_error(v->pos,"undefined variable %s",S_name(v->u.simple));
                    return expTy(NULL,Ty_Int());
                }
            }
	    case A_fieldVar:
            {
                struct expty var = transVar(venv, tenv, v->u.field.var);
                if (!(var.ty->kind == Ty_record)) 
		{
                    EM_error(v->u.field.var->pos, "not a record type");
                    return expTy(NULL,Ty_Int());
                } 
		else 
		{
                    for (Ty_fieldList field = var.ty->u.record; field; field = field->tail) 
		    {
                        if (field->head->name == v->u.field.sym) 
                            return expTy(NULL,field->head->ty);
                    }
                    EM_error(v->u.field.var->pos, "field %s doesn't exist", S_name(v->u.field.sym));
                    return expTy(NULL,Ty_Int());
                }
            }
	    case A_subscriptVar: 
	    {
		struct expty var = transVar(venv, tenv, v->u.subscript.var);
		struct expty index = transExp(venv, tenv, v->u.subscript.exp);
		if (var.ty->kind != Ty_array) 
		{
		    EM_error(v->pos, "array type required");
		    return expTy(NULL, Ty_Int());
		}
		if (index.ty->kind != Ty_int) 
		{
		    EM_error(v->pos, "index type is not int");
		    return expTy(NULL, Ty_Int());
		}
		return expTy(NULL, actual_ty(var.ty->u.array));
	    }
    	}
}

struct expty transExp(S_table venv, S_table tenv, A_exp a) 
{
	switch(a->kind) {
            case A_varExp:
                return transVar(venv, tenv, a->u.var);
            case A_nilExp:
            	return expTy(NULL,Ty_Nil());
            case A_intExp:
            	return expTy(NULL,Ty_Int());
            case A_stringExp:
            	return expTy(NULL,Ty_String());
	    case A_opExp:
            {
                A_oper oper = get_opexp_oper(a);
                struct expty left = transExp(venv, tenv, get_opexp_left(a));
		struct expty right = transExp(venv, tenv, get_opexp_right(a));
                if (oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp) 
		{
                    if (get_expty_kind(left) != Ty_int) 
                        EM_error(get_opexp_leftpos(a), "integer required");
                    if (get_expty_kind(right) != Ty_int) 
                        EM_error(get_opexp_rightpos(a), "integer required");
                }
		else if (actual_ty(left.ty) != actual_ty(right.ty))
			EM_error(a->pos, "same type required");
		return expTy(NULL,Ty_Int());
            }
	    case A_whileExp:
            {
                struct expty test = transExp(venv, tenv,get_whileexp_test(a));
                struct expty body = transExp(venv, tenv,get_whileexp_body(a));
                if (body.ty->kind != Ty_void)
                    EM_error(a->u.whilee.body->pos, "while body must produce no value");
                return expTy(NULL,Ty_Void());
            }
	    case A_forExp:
            {
                struct expty lo = transExp(venv,tenv,get_forexp_lo(a));
                struct expty hi = transExp(venv,tenv,get_forexp_hi(a));
                if (lo.ty->kind != Ty_int)
                    EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
                if (hi.ty->kind != Ty_int) 
                    EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
                S_beginScope(venv);
                S_enter(venv,a->u.forr.var,E_VarEntry(Ty_Int(),1));
                struct expty body = transExp(venv, tenv,get_forexp_body(a));
                if (get_expty_kind(body) != Ty_void) 
                    EM_error(a->u.forr.body->pos, "while body must produce no value");
                S_endScope(venv);
                return expTy(NULL,Ty_Void());
            }
	    case A_assignExp:
            {
                struct expty var = transVar(venv,tenv,get_assexp_var(a));
                struct expty exp = transExp(venv,tenv,get_assexp_exp(a));
		if (isLoopVar(venv, a->u.assign.var))
		    EM_error(a->pos, "loop variable can't be assigned");

		if (actual_ty(var.ty) != actual_ty(exp.ty)) 
		    EM_error(a->pos, "unmatched assign exp");
                return expTy(NULL,Ty_Void());
            }
	    case A_ifExp:
            {
                struct expty test = transExp(venv, tenv, get_ifexp_test(a));
                if (get_expty_kind(test) != Ty_int) 
                    EM_error(a->u.iff.test->pos, "integer required");
                struct expty then = transExp(venv, tenv, get_ifexp_then(a));
                if (get_ifexp_else(a)->kind != A_nilExp) 
		{
		    struct expty elsee = transExp(venv, tenv, a->u.iff.elsee);
                    if (actual_ty(then.ty) != actual_ty(elsee.ty)) 
                        EM_error(a->pos, "then exp and else exp type mismatch");
                    return expTy(NULL,actual_ty(then.ty));
                } 
		else 
		{
		    if (then.ty->kind != Ty_void) 
                        EM_error(a->pos, "if-then exp's body must produce no value");
                    return expTy(NULL,Ty_Void());
                }
            }
	    case A_letExp: 
	    {
            	S_beginScope(venv);
            	S_beginScope(tenv);
            	for (A_decList decs = get_letexp_decs(a);decs;decs = decs->tail) 
		{
                    transDec(venv, tenv, decs->head);
            	}
            	struct expty exp = transExp(venv, tenv, get_letexp_body(a));
            	S_endScope(tenv);
            	S_endScope(venv);

		return expTy(NULL, actual_ty(exp.ty));
	    }
	    case A_seqExp:
            {
                struct expty res = expTy(NULL,Ty_Void());
                for (A_expList cur = get_seqexp_seq(a);cur;cur = cur->tail) {
                    res = transExp(venv, tenv, cur->head);
                }
                return res;
            }
	    case A_callExp:
            {
                E_enventry x = S_look(venv, get_callexp_func(a));
                if (x && x->kind == E_funEntry) 
		{
		    A_expList arg;
		    Ty_tyList formal;
                    for (arg = get_callexp_args(a),formal = get_func_tylist(x); arg && formal; arg = arg->tail, formal = formal->tail) 
		    {
                        struct expty exp = transExp(venv, tenv, arg->head);
			if (actual_ty(formal->head) != actual_ty(exp.ty)) 
			    EM_error(arg->head->pos, "para type mismatch");
				
		    }
		    if (arg) 
                        EM_error(a->pos, "too many params in function %s", S_name(get_callexp_func(a)));
                    if (formal)
                        EM_error(a->pos, "too less params in function %s", S_name(get_callexp_func(a)));
                    return expTy(NULL,x->u.fun.result);
                } 
		else 
		{
                    EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
                    return expTy(NULL,Ty_Int());
                }
            }
	    case A_recordExp:
            {
                Ty_ty ty = S_look(tenv, a->u.record.typ);
		if (!ty) 
		{
		    EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
		    return expTy(NULL, Ty_Int());
		}

                A_efieldList fields;
                Ty_fieldList record;
                for (fields = a->u.record.fields, record = ty->u.record; fields && record; fields = fields->tail, record = record->tail) 
		{
                    struct expty exp = transExp(venv, tenv, fields->head->exp);
                }
                return expTy(NULL,actual_ty(ty));
            }
	    case A_arrayExp: 
	    {
		Ty_ty type = S_look(tenv, a->u.array.typ);
		struct expty size = transExp(venv, tenv, get_arrayexp_size(a));
		struct expty init = transExp(venv, tenv, get_arrayexp_init(a));

		if (actual_ty(init.ty) != actual_ty(type->u.array)) 
			EM_error(a->pos, "type mismatch");
		return expTy(NULL, type);
	    }
	}
}

