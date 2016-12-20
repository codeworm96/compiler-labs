/*
 * main.c
 */

#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "absyn.h"
#include "errormsg.h"
#include "temp.h" /* needed by translate.h */
#include "tree.h" /* needed by frame.h */
#include "assem.h"
#include "frame.h" /* needed by translate.h and printfrags prototype */
#include "translate.h"
#include "env.h"
#include "semant.h" /* function prototype for transProg */
#include "canon.h"
#include "prabsyn.h"
#include "printtree.h"
//#include "escape.h" /* needed by escape analysis */
#include "parse.h"
#include "codegen.h"
#include "regalloc.h"

extern bool anyErrors;

static void doString(FILE *out, F_frag s)
{
    string str = s->u.stringg.str;
    assert(s->kind == F_stringFrag);
    fprintf(out, ".section .rodata\n");
    fprintf(out, "%s:\n", Temp_labelstring(s->u.stringg.label));
    fprintf(out, ".int %d\n", strlen(str));
    fprintf(out, ".ascii \"");
    for (; *str != 0; ++str) {
        if (*str == '\n') {
            fprintf(out, "\\n");
        } else if (*str == '\t') {
            fprintf(out, "\\t");
        } else if (*str == '\\') {
            fprintf(out, "\\\\");
        } else if (*str == '\"') {
            fprintf(out, "\\\"");
        } else if (isprint(*str)) {
            fprintf(out, "%c", *str);
        } else {
            fprintf(out, "\%d%d%d", *str / 64 % 8, *str / 8 % 8, *str % 8); 
        }
    }
    fprintf(out, "\"\n");
}


/* print the assembly language instructions to filename.s */
static void doProc(FILE *out, F_frame frame, T_stm body)
{
 AS_proc proc;
 T_stmList stmList;
 AS_instrList iList;

 F_tempMap = Temp_empty();

 stmList = C_linearize(body);
 stmList = C_traceSchedule(C_basicBlocks(stmList));
 /* printStmList(stdout, stmList);*/
 iList  = F_codegen(frame, stmList); /* 9 */

 struct RA_result ra = RA_regAlloc(frame, iList);  /* 10, 11 */


 fprintf(out, ".text\n");
 fprintf(out, ".global %s\n", Temp_labelstring(F_name(frame)));
 fprintf(out, ".type %s, @function\n", Temp_labelstring(F_name(frame)));
 fprintf(out, "%s:\n", Temp_labelstring(F_name(frame)));
 fprintf(out, "pushl %%ebp\n");
 fprintf(out, "movl %%esp, %%ebp\n");
 fprintf(out, "subl $%d, %%esp\n", F_size(frame));
 AS_printInstrList (out, ra.il,
                       Temp_layerMap(F_tempMap,ra.coloring));
 fprintf(out, "leave\n");
 fprintf(out, "ret\n");
 fprintf(out, ".size %s, .-%s\n", Temp_labelstring(F_name(frame)), Temp_labelstring(F_name(frame)));
}

int main(int argc, string *argv)
{
 A_exp absyn_root;
 S_table base_env, base_tenv;
 F_fragList frags;
 char outfile[100];
 FILE *out = stdout;

 if (argc==2) {
   absyn_root = parse(argv[1]);
   if (!absyn_root)
     return 1;
     
#if 0
   pr_exp(out, absyn_root, 0); /* print absyn data structure */
   fprintf(out, "\n");
#endif
	//If you have implemented escape analysis, uncomment this
   //Esc_findEscape(absyn_root); /* set varDec's escape field */

   frags = SEM_transProg(absyn_root);
   if (anyErrors) return 1; /* don't continue */

   /* convert the filename */
   sprintf(outfile, "%s.s", argv[1]);
   out = fopen(outfile, "w");
   /* Chapter 8, 9, 10, 11 & 12 */
   for (;frags;frags=frags->tail)
     if (frags->head->kind == F_procFrag) 
       doProc(out, frags->head->u.proc.frame, frags->head->u.proc.body);
     else if (frags->head->kind == F_stringFrag) {
       doString(out, frags->head);
     }

   fclose(out);
   return 0;
 }
 EM_error(0,"usage: tiger file.tig");
 return 1;
}
