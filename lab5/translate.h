#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "frame.h"
#include "temp.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;
Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

typedef struct Tr_level_ *Tr_level;
Tr_level Tr_outermost(void);
Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);
Tr_access Tr_allocLocal(Tr_level level, bool escape);

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);
F_fragList Tr_getResult(void);

Tr_exp Tr_Nop();
Tr_exp Tr_Nil();
Tr_exp Tr_Int(int v);
Tr_exp Tr_String(string s);

void Tr_Func(Tr_exp body);

#endif
