// Lean compiler output
// Module: Std.Tactic.Do.ProofMode
// Imports: public import Std.Do.SPred.SPred
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
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__2;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__9;
LEAN_EXPORT lean_object* l_Std_Tactic_Do_mgoalHyp;
LEAN_EXPORT lean_object* l_Std_Tactic_Do_mgoalStx;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__17;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__7;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__16;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__10;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__0;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__14;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__6;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__1;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__13;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__3;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__1;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__13;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__7;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__8;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__17;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__4;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__9;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__4;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__3;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__11;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__14;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__11;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__15;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__12;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__6;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__2;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__18;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__5;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__15;
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__8;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_Do_mgoalHyp___closed__16;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__10;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__12;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__5;
static lean_object* l_Std_Tactic_Do_mgoalStx___closed__0;
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mgoalHyp", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Do", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__0;
x_2 = l_Std_Tactic_Do_mgoalHyp___closed__3;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__2;
x_4 = l_Std_Tactic_Do_mgoalHyp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__10;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__11;
x_2 = l_Std_Tactic_Do_mgoalHyp___closed__9;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Tactic_Do_mgoalHyp___closed__14;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__15;
x_2 = l_Std_Tactic_Do_mgoalHyp___closed__12;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__16;
x_2 = l_Std_Tactic_Do_mgoalHyp___closed__4;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalHyp() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__17;
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mgoalStx", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__0;
x_2 = l_Std_Tactic_Do_mgoalHyp___closed__3;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__2;
x_4 = l_Std_Tactic_Do_mgoalHyp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppDedent", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppLine", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalHyp;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__8;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__9;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__10;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⊢ₛ ", 7, 3);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__13;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__8;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalHyp___closed__15;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__14;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__15;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__16;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__11;
x_3 = l_Std_Tactic_Do_mgoalHyp___closed__6;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__17;
x_2 = l_Std_Tactic_Do_mgoalStx___closed__1;
x_3 = l_Std_Tactic_Do_mgoalStx___closed__0;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_Do_mgoalStx() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Tactic_Do_mgoalStx___closed__18;
return x_1;
}
}
lean_object* initialize_Std_Do_SPred_SPred(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_Do_ProofMode(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_SPred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_Do_mgoalHyp___closed__0 = _init_l_Std_Tactic_Do_mgoalHyp___closed__0();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__0);
l_Std_Tactic_Do_mgoalHyp___closed__1 = _init_l_Std_Tactic_Do_mgoalHyp___closed__1();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__1);
l_Std_Tactic_Do_mgoalHyp___closed__2 = _init_l_Std_Tactic_Do_mgoalHyp___closed__2();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__2);
l_Std_Tactic_Do_mgoalHyp___closed__3 = _init_l_Std_Tactic_Do_mgoalHyp___closed__3();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__3);
l_Std_Tactic_Do_mgoalHyp___closed__4 = _init_l_Std_Tactic_Do_mgoalHyp___closed__4();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__4);
l_Std_Tactic_Do_mgoalHyp___closed__5 = _init_l_Std_Tactic_Do_mgoalHyp___closed__5();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__5);
l_Std_Tactic_Do_mgoalHyp___closed__6 = _init_l_Std_Tactic_Do_mgoalHyp___closed__6();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__6);
l_Std_Tactic_Do_mgoalHyp___closed__7 = _init_l_Std_Tactic_Do_mgoalHyp___closed__7();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__7);
l_Std_Tactic_Do_mgoalHyp___closed__8 = _init_l_Std_Tactic_Do_mgoalHyp___closed__8();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__8);
l_Std_Tactic_Do_mgoalHyp___closed__9 = _init_l_Std_Tactic_Do_mgoalHyp___closed__9();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__9);
l_Std_Tactic_Do_mgoalHyp___closed__10 = _init_l_Std_Tactic_Do_mgoalHyp___closed__10();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__10);
l_Std_Tactic_Do_mgoalHyp___closed__11 = _init_l_Std_Tactic_Do_mgoalHyp___closed__11();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__11);
l_Std_Tactic_Do_mgoalHyp___closed__12 = _init_l_Std_Tactic_Do_mgoalHyp___closed__12();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__12);
l_Std_Tactic_Do_mgoalHyp___closed__13 = _init_l_Std_Tactic_Do_mgoalHyp___closed__13();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__13);
l_Std_Tactic_Do_mgoalHyp___closed__14 = _init_l_Std_Tactic_Do_mgoalHyp___closed__14();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__14);
l_Std_Tactic_Do_mgoalHyp___closed__15 = _init_l_Std_Tactic_Do_mgoalHyp___closed__15();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__15);
l_Std_Tactic_Do_mgoalHyp___closed__16 = _init_l_Std_Tactic_Do_mgoalHyp___closed__16();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__16);
l_Std_Tactic_Do_mgoalHyp___closed__17 = _init_l_Std_Tactic_Do_mgoalHyp___closed__17();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp___closed__17);
l_Std_Tactic_Do_mgoalHyp = _init_l_Std_Tactic_Do_mgoalHyp();
lean_mark_persistent(l_Std_Tactic_Do_mgoalHyp);
l_Std_Tactic_Do_mgoalStx___closed__0 = _init_l_Std_Tactic_Do_mgoalStx___closed__0();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__0);
l_Std_Tactic_Do_mgoalStx___closed__1 = _init_l_Std_Tactic_Do_mgoalStx___closed__1();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__1);
l_Std_Tactic_Do_mgoalStx___closed__2 = _init_l_Std_Tactic_Do_mgoalStx___closed__2();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__2);
l_Std_Tactic_Do_mgoalStx___closed__3 = _init_l_Std_Tactic_Do_mgoalStx___closed__3();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__3);
l_Std_Tactic_Do_mgoalStx___closed__4 = _init_l_Std_Tactic_Do_mgoalStx___closed__4();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__4);
l_Std_Tactic_Do_mgoalStx___closed__5 = _init_l_Std_Tactic_Do_mgoalStx___closed__5();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__5);
l_Std_Tactic_Do_mgoalStx___closed__6 = _init_l_Std_Tactic_Do_mgoalStx___closed__6();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__6);
l_Std_Tactic_Do_mgoalStx___closed__7 = _init_l_Std_Tactic_Do_mgoalStx___closed__7();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__7);
l_Std_Tactic_Do_mgoalStx___closed__8 = _init_l_Std_Tactic_Do_mgoalStx___closed__8();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__8);
l_Std_Tactic_Do_mgoalStx___closed__9 = _init_l_Std_Tactic_Do_mgoalStx___closed__9();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__9);
l_Std_Tactic_Do_mgoalStx___closed__10 = _init_l_Std_Tactic_Do_mgoalStx___closed__10();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__10);
l_Std_Tactic_Do_mgoalStx___closed__11 = _init_l_Std_Tactic_Do_mgoalStx___closed__11();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__11);
l_Std_Tactic_Do_mgoalStx___closed__12 = _init_l_Std_Tactic_Do_mgoalStx___closed__12();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__12);
l_Std_Tactic_Do_mgoalStx___closed__13 = _init_l_Std_Tactic_Do_mgoalStx___closed__13();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__13);
l_Std_Tactic_Do_mgoalStx___closed__14 = _init_l_Std_Tactic_Do_mgoalStx___closed__14();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__14);
l_Std_Tactic_Do_mgoalStx___closed__15 = _init_l_Std_Tactic_Do_mgoalStx___closed__15();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__15);
l_Std_Tactic_Do_mgoalStx___closed__16 = _init_l_Std_Tactic_Do_mgoalStx___closed__16();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__16);
l_Std_Tactic_Do_mgoalStx___closed__17 = _init_l_Std_Tactic_Do_mgoalStx___closed__17();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__17);
l_Std_Tactic_Do_mgoalStx___closed__18 = _init_l_Std_Tactic_Do_mgoalStx___closed__18();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx___closed__18);
l_Std_Tactic_Do_mgoalStx = _init_l_Std_Tactic_Do_mgoalStx();
lean_mark_persistent(l_Std_Tactic_Do_mgoalStx);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
