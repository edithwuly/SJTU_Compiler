#ifndef __SEMANT_H_
#define __SEMANT_H_

#include "absyn.h"
#include "symbol.h"
#include "translate.h"

struct expty;

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level level, Temp_label label);
struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level, Temp_label label);
void		 transDec(S_table venv, S_table tenv, A_dec d, Tr_level level, Temp_label label);

//void SEM_transProg(A_exp exp);
F_fragList SEM_transProg(A_exp exp);

#endif
