#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

//Lab 6: your code here
AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    return AS_InstrList(AS_Move("mov", NULL, NULL), NULL);
}


