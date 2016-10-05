%{
#include <string.h>
#include "util.h"
#include "tokens.h"
#include "errormsg.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}
/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

%}

  /* You can add lex definitions here. */
letter [a-zA-Z]
digit [0-9]

%Start NORMAL COMMENT STR

%%
  /* 
  * Below are some examples, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 
  /*
    [0-9]+	 {adjust(); yylval.ival=atoi(yytext); return INT;}
  */

<NORMAL>"while" {adjust(); return WHILE;}
<NORMAL>"for" {adjust(); return FOR;}
<NORMAL>"to" {adjust(); return TO;}
<NORMAL>"break" {adjust(); return BREAK;}
<NORMAL>"let" {adjust(); return LET;}
<NORMAL>"in" {adjust(); return IN;}
<NORMAL>"end" {adjust(); return END;}
<NORMAL>"function" {adjust(); return FUNCTION;}
<NORMAL>"var" {adjust(); return VAR;}
<NORMAL>"type" {adjust(); return TYPE;}
<NORMAL>"array" {adjust(); return ARRAY;}
<NORMAL>"if" {adjust(); return IF;}
<NORMAL>"then" {adjust(); return THEN;}
<NORMAL>"else" {adjust(); return ELSE;}
<NORMAL>"do" {adjust(); return DO;}
<NORMAL>"of" {adjust(); return OF;}
<NORMAL>"nil" {adjust(); return NIL;}

<NORMAL>"/*" {adjust(); BEGIN COMMENT;}

<NORMAL>":=" {adjust(); return ASSIGN;}
<NORMAL>"<>" {adjust(); return NEQ;}
<NORMAL>"<=" {adjust(); return LE;}
<NORMAL>">=" {adjust(); return GE;}
<NORMAL>"<" {adjust(); return LT;}
<NORMAL>">" {adjust(); return GT;}
<NORMAL>"=" {adjust(); return EQ;}
<NORMAL>"," {adjust(); return COMMA;}
<NORMAL>":" {adjust(); return COLON;}
<NORMAL>";" {adjust(); return SEMICOLON;}
<NORMAL>"(" {adjust(); return LPAREN;}
<NORMAL>")" {adjust(); return RPAREN;}
<NORMAL>"[" {adjust(); return LBRACK;}
<NORMAL>"]" {adjust(); return RBRACK;}
<NORMAL>"{" {adjust(); return LBRACE;}
<NORMAL>"}" {adjust(); return RBRACE;}
<NORMAL>"." {adjust(); return DOT;}
<NORMAL>"+" {adjust(); return PLUS;}
<NORMAL>"-" {adjust(); return MINUS;}
<NORMAL>"*" {adjust(); return TIMES;}
<NORMAL>"/" {adjust(); return DIVIDE;}
<NORMAL>"&" {adjust(); return AND;}
<NORMAL>"|" {adjust(); return OR;}

<NORMAL>" "|\t {adjust(); continue;} 
<NORMAL>\n {adjust(); EM_newline(); continue;}

<NORMAL>letter(letter|digit|_)* {adjust(); yylval.sval=yytext; return ID;}

<NORMAL>. {adjust(); EM_error(EM_tokPos, "illegal token");}
<COMMENT>"*/" {adjust(); BEGIN NORMAL;}
<COMMENT>. {adjust();}
. {BEGIN NORMAL; yyless(1);}

