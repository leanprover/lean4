// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.ToExpr
// Imports: Init.Grind.AC Lean.ToExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instToExprExpr;
static lean_object* l_Lean_Meta_Grind_AC_ofExpr___closed__3;
static lean_object* l_Lean_Meta_Grind_AC_ofExpr___closed__0;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_instToExprSeq;
static lean_object* l_Lean_Meta_Grind_AC_ofExpr___closed__2;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__7;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__5;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__6;
static lean_object* l_Lean_Meta_Grind_AC_ofExpr___closed__1;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__9;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_instToExprSeq___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ofSeq(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__4;
static lean_object* l_Lean_Meta_Grind_AC_instToExprSeq___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_ofExpr___closed__4;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__1;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__3;
static lean_object* l_Lean_Meta_Grind_AC_instToExprExpr___closed__0;
static lean_object* l_Lean_Meta_Grind_AC_instToExprSeq___closed__3;
static lean_object* l_Lean_Meta_Grind_AC_instToExprSeq___closed__0;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__0;
static lean_object* l_Lean_Meta_Grind_AC_instToExprExpr___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__8;
static lean_object* l_Lean_Meta_Grind_AC_ofExpr___closed__5;
static lean_object* l_Lean_Meta_Grind_AC_ofSeq___closed__2;
static lean_object* l_Lean_Meta_Grind_AC_instToExprExpr___closed__1;
static lean_object* l_Lean_Meta_Grind_AC_instToExprExpr___closed__3;
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("AC", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Seq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_AC_ofSeq___closed__4;
x_2 = l_Lean_Meta_Grind_AC_ofSeq___closed__3;
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__2;
x_4 = l_Lean_Meta_Grind_AC_ofSeq___closed__1;
x_5 = l_Lean_Meta_Grind_AC_ofSeq___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_ofSeq___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cons", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_AC_ofSeq___closed__7;
x_2 = l_Lean_Meta_Grind_AC_ofSeq___closed__3;
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__2;
x_4 = l_Lean_Meta_Grind_AC_ofSeq___closed__1;
x_5 = l_Lean_Meta_Grind_AC_ofSeq___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofSeq___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_ofSeq___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ofSeq(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__6;
x_4 = l_Lean_mkNatLit(x_2);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_Meta_Grind_AC_ofSeq___closed__9;
x_9 = l_Lean_mkNatLit(x_6);
x_10 = l_Lean_Meta_Grind_AC_ofSeq(x_7);
x_11 = l_Lean_mkAppB(x_8, x_9, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_ofSeq), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_AC_ofSeq___closed__3;
x_2 = l_Lean_Meta_Grind_AC_ofSeq___closed__2;
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__1;
x_4 = l_Lean_Meta_Grind_AC_ofSeq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_instToExprSeq___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_AC_instToExprSeq___closed__2;
x_2 = l_Lean_Meta_Grind_AC_instToExprSeq___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprSeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instToExprSeq___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_AC_ofSeq___closed__4;
x_2 = l_Lean_Meta_Grind_AC_ofExpr___closed__0;
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__2;
x_4 = l_Lean_Meta_Grind_AC_ofSeq___closed__1;
x_5 = l_Lean_Meta_Grind_AC_ofSeq___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_ofExpr___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("op", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_AC_ofExpr___closed__3;
x_2 = l_Lean_Meta_Grind_AC_ofExpr___closed__0;
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__2;
x_4 = l_Lean_Meta_Grind_AC_ofSeq___closed__1;
x_5 = l_Lean_Meta_Grind_AC_ofSeq___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_ofExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_ofExpr___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_ofExpr(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Grind_AC_ofExpr___closed__2;
x_4 = l_Lean_mkNatLit(x_2);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_Meta_Grind_AC_ofExpr___closed__5;
x_9 = l_Lean_Meta_Grind_AC_ofExpr(x_6);
x_10 = l_Lean_Meta_Grind_AC_ofExpr(x_7);
x_11 = l_Lean_mkAppB(x_8, x_9, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_ofExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_AC_ofExpr___closed__0;
x_2 = l_Lean_Meta_Grind_AC_ofSeq___closed__2;
x_3 = l_Lean_Meta_Grind_AC_ofSeq___closed__1;
x_4 = l_Lean_Meta_Grind_AC_ofSeq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_AC_instToExprExpr___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_AC_instToExprExpr___closed__2;
x_2 = l_Lean_Meta_Grind_AC_instToExprExpr___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_AC_instToExprExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_AC_instToExprExpr___closed__3;
return x_1;
}
}
lean_object* initialize_Init_Grind_AC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_AC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_AC_ofSeq___closed__0 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__0);
l_Lean_Meta_Grind_AC_ofSeq___closed__1 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__1);
l_Lean_Meta_Grind_AC_ofSeq___closed__2 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__2);
l_Lean_Meta_Grind_AC_ofSeq___closed__3 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__3);
l_Lean_Meta_Grind_AC_ofSeq___closed__4 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__4);
l_Lean_Meta_Grind_AC_ofSeq___closed__5 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__5);
l_Lean_Meta_Grind_AC_ofSeq___closed__6 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__6);
l_Lean_Meta_Grind_AC_ofSeq___closed__7 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__7);
l_Lean_Meta_Grind_AC_ofSeq___closed__8 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__8);
l_Lean_Meta_Grind_AC_ofSeq___closed__9 = _init_l_Lean_Meta_Grind_AC_ofSeq___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofSeq___closed__9);
l_Lean_Meta_Grind_AC_instToExprSeq___closed__0 = _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprSeq___closed__0);
l_Lean_Meta_Grind_AC_instToExprSeq___closed__1 = _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprSeq___closed__1);
l_Lean_Meta_Grind_AC_instToExprSeq___closed__2 = _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprSeq___closed__2);
l_Lean_Meta_Grind_AC_instToExprSeq___closed__3 = _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprSeq___closed__3);
l_Lean_Meta_Grind_AC_instToExprSeq = _init_l_Lean_Meta_Grind_AC_instToExprSeq();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprSeq);
l_Lean_Meta_Grind_AC_ofExpr___closed__0 = _init_l_Lean_Meta_Grind_AC_ofExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofExpr___closed__0);
l_Lean_Meta_Grind_AC_ofExpr___closed__1 = _init_l_Lean_Meta_Grind_AC_ofExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofExpr___closed__1);
l_Lean_Meta_Grind_AC_ofExpr___closed__2 = _init_l_Lean_Meta_Grind_AC_ofExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofExpr___closed__2);
l_Lean_Meta_Grind_AC_ofExpr___closed__3 = _init_l_Lean_Meta_Grind_AC_ofExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofExpr___closed__3);
l_Lean_Meta_Grind_AC_ofExpr___closed__4 = _init_l_Lean_Meta_Grind_AC_ofExpr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofExpr___closed__4);
l_Lean_Meta_Grind_AC_ofExpr___closed__5 = _init_l_Lean_Meta_Grind_AC_ofExpr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_AC_ofExpr___closed__5);
l_Lean_Meta_Grind_AC_instToExprExpr___closed__0 = _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprExpr___closed__0);
l_Lean_Meta_Grind_AC_instToExprExpr___closed__1 = _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprExpr___closed__1);
l_Lean_Meta_Grind_AC_instToExprExpr___closed__2 = _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprExpr___closed__2);
l_Lean_Meta_Grind_AC_instToExprExpr___closed__3 = _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprExpr___closed__3);
l_Lean_Meta_Grind_AC_instToExprExpr = _init_l_Lean_Meta_Grind_AC_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
