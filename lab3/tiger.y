%{
#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h" 
#include "errormsg.h"
#include "absyn.h"

int yylex(void); /* function prototype */

A_exp absyn_root;

void yyerror(char *s)
{
 EM_error(EM_tokPos, "%s", s);
 exit(1);
}
%}


%union {
	int pos;
	int ival;
	string sval;
	A_var var;
	A_exp exp;
        A_expList explist;
        A_efieldList efieldlist;
        A_decList declist;
        A_dec dec;
        A_nametyList nametylist;
        A_namety namety;
        A_ty ty;
        A_fieldList fieldlist;
        A_field field;
        A_fundec fundec;
        A_fundecList fundeclist;
	/* et cetera */
	}

%token <sval> ID STRING
%token <ival> INT

%token 
  COMMA COLON SEMICOLON LPAREN RPAREN LBRACK RBRACK 
  LBRACE RBRACE DOT 
  PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE UMINUS
  AND OR ASSIGN
  ARRAY IF THEN ELSE WHILE FOR TO DO LET IN END OF 
  BREAK NIL
  FUNCTION VAR TYPE 

%type <exp> exp program
%type <var> lvalue
%type <explist> expseq
%type <explist> exps
%type <explist> params
%type <explist> param
%type <efieldlist> rec
%type <efieldlist> recs
%type <dec> dec
%type <nametylist> tydecs
%type <fundeclist> fundecs
%type <dec> vardec
%type <declist> decs
%type <namety> tydec
%type <ty> ty
%type <fieldlist> tyfields
%type <fieldlist> tyf
%type <fundec> fundec
/* et cetera */

%start program

%nonassoc DO

%nonassoc THEN
%nonassoc ELSE

%nonassoc OF

%nonassoc ASSIGN
%left OR
%left AND
%nonassoc EQ NEQ LT GT LE GE
%left PLUS MINUS
%left TIMES DIVIDE
%left UMINUS

%%

program:   exp    {absyn_root=$1;};

exp: lvalue {$$=A_VarExp(EM_tokPos, $1);}
   | NIL {$$=A_NilExp(EM_tokPos);}
   | INT {$$=A_IntExp(EM_tokPos, $1);}
   | STRING {$$=A_StringExp(EM_tokPos, $1);}
   | BREAK {$$=A_BreakExp(EM_tokPos);}
   | MINUS exp %prec UMINUS {$$=A_OpExp(EM_tokPos, A_minusOp, A_IntExp(EM_tokPos, 0), $2);}
   | LPAREN expseq RPAREN {$$=A_SeqExp(EM_tokPos,$2);}
   | IF exp THEN exp ELSE exp {$$=A_IfExp(EM_tokPos, $2, $4, $6);}
   | IF exp THEN exp {$$=A_IfExp(EM_tokPos, $2, $4, A_NilExp(EM_tokPos));}
   | WHILE exp DO exp {$$=A_WhileExp(EM_tokPos, $2, $4);}
   | FOR ID ASSIGN exp TO exp DO exp {$$=A_ForExp(EM_tokPos, S_Symbol($2), $4, $6, $8);}
   | LET decs IN expseq END {$$=A_LetExp(EM_tokPos, $2, A_SeqExp(EM_tokPos, $4));}
   | ID LBRACK exp RBRACK OF exp {$$=A_ArrayExp(EM_tokPos, S_Symbol($1), $3, $6);}
   | ID LBRACE rec RBRACE {$$=A_RecordExp(EM_tokPos, S_Symbol($1), $3);}
   | ID LPAREN params RPAREN {$$=A_CallExp(EM_tokPos, S_Symbol($1), $3);}
   | exp PLUS exp {$$=A_OpExp(EM_tokPos, A_plusOp, $1, $3);}
   | exp MINUS exp {$$=A_OpExp(EM_tokPos, A_minusOp, $1, $3);}
   | exp TIMES exp {$$=A_OpExp(EM_tokPos, A_timesOp, $1, $3);}
   | exp DIVIDE exp {$$=A_OpExp(EM_tokPos, A_divideOp, $1, $3);}
   | exp EQ exp {$$=A_OpExp(EM_tokPos, A_eqOp, $1, $3);}
   | exp NEQ exp {$$=A_OpExp(EM_tokPos, A_neqOp, $1, $3);}
   | exp LT exp {$$=A_OpExp(EM_tokPos, A_ltOp, $1, $3);}
   | exp LE exp {$$=A_OpExp(EM_tokPos, A_leOp, $1, $3);}
   | exp GT exp {$$=A_OpExp(EM_tokPos, A_gtOp, $1, $3);}
   | exp GE exp {$$=A_OpExp(EM_tokPos, A_geOp, $1, $3);}
   | exp AND exp {$$=A_IfExp(EM_tokPos, $1, $3, A_IntExp(EM_tokPos, 0));}
   | exp OR exp {$$=A_IfExp(EM_tokPos, $1, A_IntExp(EM_tokPos, 1), $3);}
   | lvalue ASSIGN exp {$$=A_AssignExp(EM_tokPos, $1, $3);}
   ;

rec: {$$=NULL;}
   | recs {$$=$1;}
   ;

recs: ID EQ exp {$$=A_EfieldList(A_Efield(S_Symbol($1), $3), NULL);}
    | ID EQ exp COMMA recs {$$=A_EfieldList(A_Efield(S_Symbol($1), $3), $5);}
    ;

expseq: {$$=NULL;}
      | exps {$$=$1;}
      ;

exps: exp {$$=A_ExpList($1, NULL);}
    | exp SEMICOLON exps {$$=A_ExpList($1, $3);}
    ;

params: {$$=NULL;}
      | param {$$=$1;}
      ;

param: exp {$$=A_ExpList($1, NULL);}
     | exp COMMA param {$$=A_ExpList($1, $3);}
     ;

decs: {$$=NULL;}
    | dec decs {$$=A_DecList($1, $2);}
    ;

dec: tydecs {$$=A_TypeDec(EM_tokPos, $1);}
   | vardec {$$=$1;}
   | fundecs {$$=A_FunctionDec(EM_tokPos, $1);}
   ;

tydecs: tydec {$$=A_NametyList($1, NULL);}
      | tydec tydecs {$$=A_NametyList($1, $2);}
      ;

tydec: TYPE ID EQ ty {$$=A_Namety(S_Symbol($2), $4);};

ty: ID {$$=A_NameTy(EM_tokPos, S_Symbol($1));}
  | LBRACE tyfields RBRACE {$$=A_RecordTy(EM_tokPos, $2);}
  | ARRAY OF ID {$$=A_ArrayTy(EM_tokPos, S_Symbol($3));}
  ;

tyfields: {$$=NULL;}
        | tyf {$$=$1;}
        ;

tyf: ID COLON ID {$$=A_FieldList(A_Field(EM_tokPos, S_Symbol($1), S_Symbol($3)), NULL);}
   | ID COLON ID COMMA tyf {$$=A_FieldList(A_Field(EM_tokPos, S_Symbol($1), S_Symbol($3)), $5);}
   ;

vardec: VAR ID ASSIGN exp {$$=A_VarDec(EM_tokPos, S_Symbol($2), NULL, $4);}
      | VAR ID COLON ID ASSIGN exp {$$=A_VarDec(EM_tokPos, S_Symbol($2), S_Symbol($4), $6);}
      ;

fundecs: fundec {$$=A_FundecList($1, NULL);}
       | fundec fundecs {$$=A_FundecList($1, $2);}
       ;

fundec: FUNCTION ID LPAREN tyfields RPAREN EQ exp {$$=A_Fundec(EM_tokPos, S_Symbol($2), $4, NULL, $7);}
      | FUNCTION ID LPAREN tyfields RPAREN COLON ID EQ exp {$$=A_Fundec(EM_tokPos, S_Symbol($2), $4, S_Symbol($7), $9);}
      ;	

lvalue: ID {$$=A_SimpleVar(EM_tokPos, S_Symbol($1));}
      | lvalue DOT ID {$$=A_FieldVar(EM_tokPos, $1, S_Symbol($3));}
      | lvalue LBRACK exp RBRACK {$$=A_SubscriptVar(EM_tokPos, $1, $3);}
      | ID LBRACK exp RBRACK {$$=A_SubscriptVar(EM_tokPos, A_SimpleVar(EM_tokPos, S_Symbol($1)), $3);}
      ;

