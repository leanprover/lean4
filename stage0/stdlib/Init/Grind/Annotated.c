// Lean compiler output
// Module: Init.Grind.Annotated
// Imports: public import Init.Tactics
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
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__3;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__13;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__2;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__12;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__4;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__7;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__0;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__8;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_grindAnnotated;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__10;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__11;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__5;
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Command_grindAnnotated___closed__9;
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindAnnotated", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__3;
x_2 = l_Lean_Parser_Command_grindAnnotated___closed__2;
x_3 = l_Lean_Parser_Command_grindAnnotated___closed__1;
x_4 = l_Lean_Parser_Command_grindAnnotated___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind_annotated", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__11;
x_2 = l_Lean_Parser_Command_grindAnnotated___closed__8;
x_3 = l_Lean_Parser_Command_grindAnnotated___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__12;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Parser_Command_grindAnnotated___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Command_grindAnnotated() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Command_grindAnnotated___closed__13;
return x_1;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Annotated(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Command_grindAnnotated___closed__0 = _init_l_Lean_Parser_Command_grindAnnotated___closed__0();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__0);
l_Lean_Parser_Command_grindAnnotated___closed__1 = _init_l_Lean_Parser_Command_grindAnnotated___closed__1();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__1);
l_Lean_Parser_Command_grindAnnotated___closed__2 = _init_l_Lean_Parser_Command_grindAnnotated___closed__2();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__2);
l_Lean_Parser_Command_grindAnnotated___closed__3 = _init_l_Lean_Parser_Command_grindAnnotated___closed__3();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__3);
l_Lean_Parser_Command_grindAnnotated___closed__4 = _init_l_Lean_Parser_Command_grindAnnotated___closed__4();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__4);
l_Lean_Parser_Command_grindAnnotated___closed__5 = _init_l_Lean_Parser_Command_grindAnnotated___closed__5();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__5);
l_Lean_Parser_Command_grindAnnotated___closed__6 = _init_l_Lean_Parser_Command_grindAnnotated___closed__6();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__6);
l_Lean_Parser_Command_grindAnnotated___closed__7 = _init_l_Lean_Parser_Command_grindAnnotated___closed__7();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__7);
l_Lean_Parser_Command_grindAnnotated___closed__8 = _init_l_Lean_Parser_Command_grindAnnotated___closed__8();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__8);
l_Lean_Parser_Command_grindAnnotated___closed__9 = _init_l_Lean_Parser_Command_grindAnnotated___closed__9();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__9);
l_Lean_Parser_Command_grindAnnotated___closed__10 = _init_l_Lean_Parser_Command_grindAnnotated___closed__10();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__10);
l_Lean_Parser_Command_grindAnnotated___closed__11 = _init_l_Lean_Parser_Command_grindAnnotated___closed__11();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__11);
l_Lean_Parser_Command_grindAnnotated___closed__12 = _init_l_Lean_Parser_Command_grindAnnotated___closed__12();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__12);
l_Lean_Parser_Command_grindAnnotated___closed__13 = _init_l_Lean_Parser_Command_grindAnnotated___closed__13();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated___closed__13);
l_Lean_Parser_Command_grindAnnotated = _init_l_Lean_Parser_Command_grindAnnotated();
lean_mark_persistent(l_Lean_Parser_Command_grindAnnotated);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
