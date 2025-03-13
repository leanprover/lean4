// Lean compiler output
// Module: Init.RCases
// Imports: Init.Tactics Init.Meta
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__1;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_one___closed__6;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__5;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_one___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintroPat_quot;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__5;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__13;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__3;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__6;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__11;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__1;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__11;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__15;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcases;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_one___closed__3;
static lean_object* l_Lean_Parser_Tactic_rintroPat_one___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintroPat_one;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__6;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__2;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_clear___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__18;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintroPat_binder;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__13;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__14;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__16;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_clear;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__5;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__10;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__13;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__10;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__19;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__11;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__17;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_obtain;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__15;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__8;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__16;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__4;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__1;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_one___closed__1;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_one___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__6;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__11;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__9;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_paren;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_one___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__9;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__4;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__6;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__14;
static lean_object* l_Lean_Parser_Tactic_rintroPat_one___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_clear___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintro;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPatMed;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_clear___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__10;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__9;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_one;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
extern lean_object* l_Lean_Parser_Tactic_elimTarget;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__7;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__6;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__17;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_rintro___closed__12;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__10;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__9;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__10;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__10;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__6;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__5;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_rcasesPat;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__13;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPatLo;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__2;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__7;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_clear___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__2;
static lean_object* l_Lean_Parser_Tactic_rintroPat_binder___closed__9;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__3;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_clear___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_quot;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__2;
static lean_object* l_Lean_Parser_Tactic_rcases___closed__6;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_rintroPat;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__7;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__10;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__4;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3;
static lean_object* l_Lean_Parser_Tactic_rintro___closed__5;
static lean_object* l_Lean_Parser_Tactic_rcasesPatLo___closed__11;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_quot___closed__12;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_paren___closed__1;
static lean_object* l_Lean_Parser_Tactic_rintroPat_quot___closed__8;
static lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6;
static lean_object* l_Lean_Parser_Tactic_rcasesPatMed___closed__5;
static lean_object* l_Lean_Parser_Tactic_obtain___closed__9;
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quot", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__3;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rcasesPat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(rcasesPat| ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__10;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__14;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__13;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__11;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__17;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__18;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__19;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_rcasesPat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rcasesPatMed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPatMed___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" | ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPatMed___closed__4;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__13;
x_2 = l_Lean_Parser_Tactic_rcasesPatMed___closed__4;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__5;
x_4 = 0;
x_5 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPatMed___closed__2;
x_2 = l_Lean_Parser_Tactic_rcasesPatMed___closed__3;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__6;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPatMed___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rcasesPatLo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPatLo___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optional", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rcasesPatLo___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rcasesPatLo___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPatLo___closed__6;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__4;
x_2 = l_Lean_Parser_Tactic_rcasesPatLo___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPatMed;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPatLo___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo___closed__12;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__13;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("one", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_5 = l_Lean_Parser_Tactic_rcasesPat_one___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rcasesPat_one___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_one___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_one___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_one___closed__5;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_one___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ignore", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_5 = l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_ignore___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("clear", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_5 = l_Lean_Parser_Tactic_rcasesPat_clear___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_clear___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_clear___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_clear___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_clear___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explicit", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_5 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("noWs", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4;
x_3 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_explicit___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tuple", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_5 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo;
x_2 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7;
x_3 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6;
x_4 = 0;
x_5 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4;
x_3 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟩", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9;
x_3 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__13;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__6;
x_5 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__4;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__5;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rintroPat", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rintroPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(rintroPat| ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rintroPat_quot___closed__3;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rintroPat_quot___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rintroPat_quot___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintroPat_quot___closed__6;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintroPat_quot___closed__4;
x_3 = l_Lean_Parser_Tactic_rintroPat_quot___closed__7;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rintroPat_quot___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rintroPat_quot___closed__8;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rintroPat_quot___closed__9;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rintroPat_quot___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_rintroPat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_one___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rintroPat_quot___closed__1;
x_5 = l_Lean_Parser_Tactic_rcasesPat_one___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_one___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rintroPat_one___closed__1;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__13;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_one() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rintroPat_one___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binder", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rintroPat_quot___closed__1;
x_5 = l_Lean_Parser_Tactic_rintroPat_binder___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many1", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rintroPat_binder___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rintroPat_binder___closed__4;
x_2 = l_Lean_Parser_Tactic_rintroPat_quot___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_paren___closed__4;
x_3 = l_Lean_Parser_Tactic_rintroPat_binder___closed__5;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintroPat_binder___closed__6;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintroPat_binder___closed__7;
x_3 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rintroPat_binder___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_rintroPat_binder___closed__8;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rintroPat_binder___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rcases", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rcases___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcases___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_elimTarget;
x_2 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7;
x_3 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6;
x_4 = 0;
x_5 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcases___closed__3;
x_3 = l_Lean_Parser_Tactic_rcases___closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" with ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rcases___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcases___closed__7;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__4;
x_2 = l_Lean_Parser_Tactic_rcases___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rcases___closed__5;
x_3 = l_Lean_Parser_Tactic_rcases___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcases___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_rcases___closed__10;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rcases___closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("obtain", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_obtain___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_obtain___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppSpace", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_obtain___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_obtain___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_obtain___closed__6;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__4;
x_2 = l_Lean_Parser_Tactic_obtain___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_obtain___closed__3;
x_3 = l_Lean_Parser_Tactic_obtain___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_obtain___closed__9;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_obtain___closed__11;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__9;
x_2 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7;
x_3 = l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6;
x_4 = 0;
x_5 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_obtain___closed__12;
x_3 = l_Lean_Parser_Tactic_obtain___closed__13;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rcasesPatLo___closed__4;
x_2 = l_Lean_Parser_Tactic_obtain___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_obtain___closed__10;
x_3 = l_Lean_Parser_Tactic_obtain___closed__15;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_obtain___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_obtain___closed__16;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_obtain___closed__17;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rintro", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__1;
x_2 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__2;
x_3 = l_Lean_Parser_Tactic_rcasesPatMed___closed__1;
x_4 = l_Lean_Parser_Tactic_rintro___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rintro___closed__1;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("colGt", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_rintro___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_rintro___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_obtain___closed__6;
x_3 = l_Lean_Parser_Tactic_rintro___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintro___closed__7;
x_3 = l_Lean_Parser_Tactic_rintroPat_quot___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_rintroPat_binder___closed__4;
x_2 = l_Lean_Parser_Tactic_rintro___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintro___closed__3;
x_3 = l_Lean_Parser_Tactic_rintro___closed__9;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rcasesPat_quot___closed__9;
x_2 = l_Lean_Parser_Tactic_rintro___closed__10;
x_3 = l_Lean_Parser_Tactic_rcasesPatLo___closed__11;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_rintro___closed__2;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Tactic_rintro___closed__11;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_rintro___closed__12;
return x_1;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Meta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_RCases(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__1);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__2);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__3);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__4);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__5);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__6);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__7 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__7);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__8 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__8);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__9 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__9);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__10 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__10);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__11 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__11);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__12 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__12);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__13 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__13);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__14 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__14);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__15 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__15);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__16 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__16();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__16);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__17 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__17();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__17);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__18 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__18();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__18);
l_Lean_Parser_Tactic_rcasesPat_quot___closed__19 = _init_l_Lean_Parser_Tactic_rcasesPat_quot___closed__19();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot___closed__19);
l_Lean_Parser_Tactic_rcasesPat_quot = _init_l_Lean_Parser_Tactic_rcasesPat_quot();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot);
l_Lean_Parser_Category_rcasesPat = _init_l_Lean_Parser_Category_rcasesPat();
lean_mark_persistent(l_Lean_Parser_Category_rcasesPat);
l_Lean_Parser_Tactic_rcasesPatMed___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__1);
l_Lean_Parser_Tactic_rcasesPatMed___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__2);
l_Lean_Parser_Tactic_rcasesPatMed___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__3);
l_Lean_Parser_Tactic_rcasesPatMed___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__4);
l_Lean_Parser_Tactic_rcasesPatMed___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__5);
l_Lean_Parser_Tactic_rcasesPatMed___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__6);
l_Lean_Parser_Tactic_rcasesPatMed___closed__7 = _init_l_Lean_Parser_Tactic_rcasesPatMed___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed___closed__7);
l_Lean_Parser_Tactic_rcasesPatMed = _init_l_Lean_Parser_Tactic_rcasesPatMed();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed);
l_Lean_Parser_Tactic_rcasesPatLo___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__1);
l_Lean_Parser_Tactic_rcasesPatLo___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__2);
l_Lean_Parser_Tactic_rcasesPatLo___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__3);
l_Lean_Parser_Tactic_rcasesPatLo___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__4);
l_Lean_Parser_Tactic_rcasesPatLo___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__5);
l_Lean_Parser_Tactic_rcasesPatLo___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__6);
l_Lean_Parser_Tactic_rcasesPatLo___closed__7 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__7);
l_Lean_Parser_Tactic_rcasesPatLo___closed__8 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__8);
l_Lean_Parser_Tactic_rcasesPatLo___closed__9 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__9);
l_Lean_Parser_Tactic_rcasesPatLo___closed__10 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__10);
l_Lean_Parser_Tactic_rcasesPatLo___closed__11 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__11);
l_Lean_Parser_Tactic_rcasesPatLo___closed__12 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__12);
l_Lean_Parser_Tactic_rcasesPatLo___closed__13 = _init_l_Lean_Parser_Tactic_rcasesPatLo___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo___closed__13);
l_Lean_Parser_Tactic_rcasesPatLo = _init_l_Lean_Parser_Tactic_rcasesPatLo();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo);
l_Lean_Parser_Tactic_rcasesPat_one___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one___closed__1);
l_Lean_Parser_Tactic_rcasesPat_one___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one___closed__2);
l_Lean_Parser_Tactic_rcasesPat_one___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one___closed__3);
l_Lean_Parser_Tactic_rcasesPat_one___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one___closed__4);
l_Lean_Parser_Tactic_rcasesPat_one___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one___closed__5);
l_Lean_Parser_Tactic_rcasesPat_one___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPat_one___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one___closed__6);
l_Lean_Parser_Tactic_rcasesPat_one = _init_l_Lean_Parser_Tactic_rcasesPat_one();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one);
l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__1);
l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__2);
l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__3);
l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__4);
l_Lean_Parser_Tactic_rcasesPat_ignore___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_ignore___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore___closed__5);
l_Lean_Parser_Tactic_rcasesPat_ignore = _init_l_Lean_Parser_Tactic_rcasesPat_ignore();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore);
l_Lean_Parser_Tactic_rcasesPat_clear___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear___closed__1);
l_Lean_Parser_Tactic_rcasesPat_clear___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear___closed__2);
l_Lean_Parser_Tactic_rcasesPat_clear___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear___closed__3);
l_Lean_Parser_Tactic_rcasesPat_clear___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear___closed__4);
l_Lean_Parser_Tactic_rcasesPat_clear___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_clear___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear___closed__5);
l_Lean_Parser_Tactic_rcasesPat_clear = _init_l_Lean_Parser_Tactic_rcasesPat_clear();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__1);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__2);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__3);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__4);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__5);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__6);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__7);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__8);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__9);
l_Lean_Parser_Tactic_rcasesPat_explicit___closed__10 = _init_l_Lean_Parser_Tactic_rcasesPat_explicit___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit___closed__10);
l_Lean_Parser_Tactic_rcasesPat_explicit = _init_l_Lean_Parser_Tactic_rcasesPat_explicit();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__1);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__2);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__3);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__4);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__5);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__6);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__7);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__8);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__9);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__10);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__11);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__12);
l_Lean_Parser_Tactic_rcasesPat_tuple___closed__13 = _init_l_Lean_Parser_Tactic_rcasesPat_tuple___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple___closed__13);
l_Lean_Parser_Tactic_rcasesPat_tuple = _init_l_Lean_Parser_Tactic_rcasesPat_tuple();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__1 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__1);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__2 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__2);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__3 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__3);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__4 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__4);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__5 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__5);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__6 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__6);
l_Lean_Parser_Tactic_rcasesPat_paren___closed__7 = _init_l_Lean_Parser_Tactic_rcasesPat_paren___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren___closed__7);
l_Lean_Parser_Tactic_rcasesPat_paren = _init_l_Lean_Parser_Tactic_rcasesPat_paren();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren);
l_Lean_Parser_Tactic_rintroPat_quot___closed__1 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__1);
l_Lean_Parser_Tactic_rintroPat_quot___closed__2 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__2);
l_Lean_Parser_Tactic_rintroPat_quot___closed__3 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__3);
l_Lean_Parser_Tactic_rintroPat_quot___closed__4 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__4);
l_Lean_Parser_Tactic_rintroPat_quot___closed__5 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__5);
l_Lean_Parser_Tactic_rintroPat_quot___closed__6 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__6);
l_Lean_Parser_Tactic_rintroPat_quot___closed__7 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__7);
l_Lean_Parser_Tactic_rintroPat_quot___closed__8 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__8);
l_Lean_Parser_Tactic_rintroPat_quot___closed__9 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__9);
l_Lean_Parser_Tactic_rintroPat_quot___closed__10 = _init_l_Lean_Parser_Tactic_rintroPat_quot___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot___closed__10);
l_Lean_Parser_Tactic_rintroPat_quot = _init_l_Lean_Parser_Tactic_rintroPat_quot();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot);
l_Lean_Parser_Category_rintroPat = _init_l_Lean_Parser_Category_rintroPat();
lean_mark_persistent(l_Lean_Parser_Category_rintroPat);
l_Lean_Parser_Tactic_rintroPat_one___closed__1 = _init_l_Lean_Parser_Tactic_rintroPat_one___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_one___closed__1);
l_Lean_Parser_Tactic_rintroPat_one___closed__2 = _init_l_Lean_Parser_Tactic_rintroPat_one___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_one___closed__2);
l_Lean_Parser_Tactic_rintroPat_one = _init_l_Lean_Parser_Tactic_rintroPat_one();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_one);
l_Lean_Parser_Tactic_rintroPat_binder___closed__1 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__1);
l_Lean_Parser_Tactic_rintroPat_binder___closed__2 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__2);
l_Lean_Parser_Tactic_rintroPat_binder___closed__3 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__3);
l_Lean_Parser_Tactic_rintroPat_binder___closed__4 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__4);
l_Lean_Parser_Tactic_rintroPat_binder___closed__5 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__5);
l_Lean_Parser_Tactic_rintroPat_binder___closed__6 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__6);
l_Lean_Parser_Tactic_rintroPat_binder___closed__7 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__7);
l_Lean_Parser_Tactic_rintroPat_binder___closed__8 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__8);
l_Lean_Parser_Tactic_rintroPat_binder___closed__9 = _init_l_Lean_Parser_Tactic_rintroPat_binder___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder___closed__9);
l_Lean_Parser_Tactic_rintroPat_binder = _init_l_Lean_Parser_Tactic_rintroPat_binder();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder);
l_Lean_Parser_Tactic_rcases___closed__1 = _init_l_Lean_Parser_Tactic_rcases___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__1);
l_Lean_Parser_Tactic_rcases___closed__2 = _init_l_Lean_Parser_Tactic_rcases___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__2);
l_Lean_Parser_Tactic_rcases___closed__3 = _init_l_Lean_Parser_Tactic_rcases___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__3);
l_Lean_Parser_Tactic_rcases___closed__4 = _init_l_Lean_Parser_Tactic_rcases___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__4);
l_Lean_Parser_Tactic_rcases___closed__5 = _init_l_Lean_Parser_Tactic_rcases___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__5);
l_Lean_Parser_Tactic_rcases___closed__6 = _init_l_Lean_Parser_Tactic_rcases___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__6);
l_Lean_Parser_Tactic_rcases___closed__7 = _init_l_Lean_Parser_Tactic_rcases___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__7);
l_Lean_Parser_Tactic_rcases___closed__8 = _init_l_Lean_Parser_Tactic_rcases___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__8);
l_Lean_Parser_Tactic_rcases___closed__9 = _init_l_Lean_Parser_Tactic_rcases___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__9);
l_Lean_Parser_Tactic_rcases___closed__10 = _init_l_Lean_Parser_Tactic_rcases___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__10);
l_Lean_Parser_Tactic_rcases___closed__11 = _init_l_Lean_Parser_Tactic_rcases___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases___closed__11);
l_Lean_Parser_Tactic_rcases = _init_l_Lean_Parser_Tactic_rcases();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases);
l_Lean_Parser_Tactic_obtain___closed__1 = _init_l_Lean_Parser_Tactic_obtain___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__1);
l_Lean_Parser_Tactic_obtain___closed__2 = _init_l_Lean_Parser_Tactic_obtain___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__2);
l_Lean_Parser_Tactic_obtain___closed__3 = _init_l_Lean_Parser_Tactic_obtain___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__3);
l_Lean_Parser_Tactic_obtain___closed__4 = _init_l_Lean_Parser_Tactic_obtain___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__4);
l_Lean_Parser_Tactic_obtain___closed__5 = _init_l_Lean_Parser_Tactic_obtain___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__5);
l_Lean_Parser_Tactic_obtain___closed__6 = _init_l_Lean_Parser_Tactic_obtain___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__6);
l_Lean_Parser_Tactic_obtain___closed__7 = _init_l_Lean_Parser_Tactic_obtain___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__7);
l_Lean_Parser_Tactic_obtain___closed__8 = _init_l_Lean_Parser_Tactic_obtain___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__8);
l_Lean_Parser_Tactic_obtain___closed__9 = _init_l_Lean_Parser_Tactic_obtain___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__9);
l_Lean_Parser_Tactic_obtain___closed__10 = _init_l_Lean_Parser_Tactic_obtain___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__10);
l_Lean_Parser_Tactic_obtain___closed__11 = _init_l_Lean_Parser_Tactic_obtain___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__11);
l_Lean_Parser_Tactic_obtain___closed__12 = _init_l_Lean_Parser_Tactic_obtain___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__12);
l_Lean_Parser_Tactic_obtain___closed__13 = _init_l_Lean_Parser_Tactic_obtain___closed__13();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__13);
l_Lean_Parser_Tactic_obtain___closed__14 = _init_l_Lean_Parser_Tactic_obtain___closed__14();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__14);
l_Lean_Parser_Tactic_obtain___closed__15 = _init_l_Lean_Parser_Tactic_obtain___closed__15();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__15);
l_Lean_Parser_Tactic_obtain___closed__16 = _init_l_Lean_Parser_Tactic_obtain___closed__16();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__16);
l_Lean_Parser_Tactic_obtain___closed__17 = _init_l_Lean_Parser_Tactic_obtain___closed__17();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain___closed__17);
l_Lean_Parser_Tactic_obtain = _init_l_Lean_Parser_Tactic_obtain();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain);
l_Lean_Parser_Tactic_rintro___closed__1 = _init_l_Lean_Parser_Tactic_rintro___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__1);
l_Lean_Parser_Tactic_rintro___closed__2 = _init_l_Lean_Parser_Tactic_rintro___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__2);
l_Lean_Parser_Tactic_rintro___closed__3 = _init_l_Lean_Parser_Tactic_rintro___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__3);
l_Lean_Parser_Tactic_rintro___closed__4 = _init_l_Lean_Parser_Tactic_rintro___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__4);
l_Lean_Parser_Tactic_rintro___closed__5 = _init_l_Lean_Parser_Tactic_rintro___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__5);
l_Lean_Parser_Tactic_rintro___closed__6 = _init_l_Lean_Parser_Tactic_rintro___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__6);
l_Lean_Parser_Tactic_rintro___closed__7 = _init_l_Lean_Parser_Tactic_rintro___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__7);
l_Lean_Parser_Tactic_rintro___closed__8 = _init_l_Lean_Parser_Tactic_rintro___closed__8();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__8);
l_Lean_Parser_Tactic_rintro___closed__9 = _init_l_Lean_Parser_Tactic_rintro___closed__9();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__9);
l_Lean_Parser_Tactic_rintro___closed__10 = _init_l_Lean_Parser_Tactic_rintro___closed__10();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__10);
l_Lean_Parser_Tactic_rintro___closed__11 = _init_l_Lean_Parser_Tactic_rintro___closed__11();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__11);
l_Lean_Parser_Tactic_rintro___closed__12 = _init_l_Lean_Parser_Tactic_rintro___closed__12();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro___closed__12);
l_Lean_Parser_Tactic_rintro = _init_l_Lean_Parser_Tactic_rintro();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
