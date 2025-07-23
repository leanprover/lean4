// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
// Imports: Init.Grind.ToInt Lean.Meta.Tactic.Grind.Arith.Util
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__4;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__4;
x_5 = lean_box(0);
x_6 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 26, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_6);
lean_ctor_set(x_8, 7, x_6);
lean_ctor_set(x_8, 8, x_3);
lean_ctor_set(x_8, 9, x_6);
lean_ctor_set(x_8, 10, x_6);
lean_ctor_set(x_8, 11, x_3);
lean_ctor_set(x_8, 12, x_3);
lean_ctor_set(x_8, 13, x_2);
lean_ctor_set(x_8, 14, x_2);
lean_ctor_set(x_8, 15, x_2);
lean_ctor_set(x_8, 16, x_2);
lean_ctor_set(x_8, 17, x_1);
lean_ctor_set(x_8, 18, x_1);
lean_ctor_set(x_8, 19, x_2);
lean_ctor_set(x_8, 20, x_2);
lean_ctor_set(x_8, 21, x_2);
lean_ctor_set(x_8, 22, x_2);
lean_ctor_set(x_8, 23, x_2);
lean_ctor_set(x_8, 24, x_2);
lean_ctor_set(x_8, 25, x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__5;
return x_1;
}
}
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntThms);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedToIntInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
