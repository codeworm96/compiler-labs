#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "env.h"


E_enventry E_VarEntry(Ty_ty ty)
{
    E_enventry res = checked_malloc(sizeof(*res));
    res->kind = E_varEntry;
    res->u.var.ty = ty;
    return res;
}

E_enventry E_FunEntry(Ty_tyList formals, Ty_ty result)
{
    E_enventry res = checked_malloc(sizeof(*res));
    res->kind = E_funEntry;
    res->u.fun.formals = formals;
    res->u.fun.result = result;
    return res;
}

S_table E_base_tenv(void)
{
    S_table res = S_empty();
    S_enter(res, S_Symbol("int"), Ty_Int(0));
    S_enter(res, S_Symbol("string"), Ty_String());
    return res;
}

S_table E_base_venv(void)
{
    S_table res = S_empty();
    S_enter(res, S_Symbol("print"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Void()));
    S_enter(res, S_Symbol("flush"), E_FunEntry(NULL, Ty_Void()));
    S_enter(res, S_Symbol("getchar"), E_FunEntry(NULL, Ty_String()));
    S_enter(res, S_Symbol("ord"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int(0)));
    S_enter(res, S_Symbol("chr"), E_FunEntry(Ty_TyList(Ty_Int(0), NULL), Ty_String()));
    S_enter(res, S_Symbol("size"), E_FunEntry(Ty_TyList(Ty_String(), NULL), Ty_Int(0)));
    S_enter(res, S_Symbol("substring"), E_FunEntry(Ty_TyList(Ty_String(), Ty_TyList(Ty_Int(0), Ty_TyList(Ty_Int(0), NULL))), Ty_String()));
    S_enter(res, S_Symbol("concat"), E_FunEntry(Ty_TyList(Ty_String(), Ty_TyList(Ty_String(), NULL)), Ty_String()));
    S_enter(res, S_Symbol("not"), E_FunEntry(Ty_TyList(Ty_Int(0), NULL), Ty_Int(0)));
    S_enter(res, S_Symbol("exit"), E_FunEntry(Ty_TyList(Ty_Int(0), NULL), Ty_Void()));
    return res;
}
