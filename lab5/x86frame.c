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

struct F_frame_ {

};


F_frag F_StringFrag(Temp_label label, string str) {
    F_frag res = checked_malloc(sizeof(*res));
    res->kind = F_stringFrag;
    res->u.stringg.label = label;
    res->u.stringg.str = str;
    return res;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
    F_frag res = checked_malloc(sizeof(*res));
    res->kind = F_procFrag;
    res->u.proc.body = body;
    res->u.proc.frame = frame;
    return res;
}

F_fragList F_FragList(F_frag head, F_fragList tail) {
    F_fragList res = checked_malloc(sizeof(*res));
    res->head = head;
    res->tail = tail;
    return res;
}

