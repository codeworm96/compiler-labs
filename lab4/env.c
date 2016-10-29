#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "env.h"


E_enventry E_VarEntry(Ty_ty ty)
{
    E_enventry res = checked_malloc(sizeof(struct E_enventry_));
    res->kind = E_varEntry;
    res->u.var.ty = ty;
    return res;
}

E_enventry E_FunEntry(Ty_tyList formals, Ty_ty result)
{
    E_enventry res = checked_malloc(sizeof(struct E_enventry_));
    res->kind = E_funEntry;
    res->u.fun.formals = formals;
    res->u.fun.result = result;
    return res;
}

S_table E_base_tenv(void)
{
    return S_empty();
}

S_table E_base_venv(void)
{
    return S_empty();
}
