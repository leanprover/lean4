// Lean compiler output
// Module: Lean.Meta.Tactic.LinearArith.Simp
// Imports: Init Lean.Meta.Tactic.LinearArith.Basic Lean.Meta.Tactic.LinearArith.Nat.Simp
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
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__3;
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__1;
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__10;
lean_object* l_Lean_Meta_Linear_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Linear_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__7;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LinearArith_Simp_0__Lean_Meta_Linear_parentIsTarget___boxed(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LinearArith_Simp_0__Lean_Meta_Linear_parentIsTarget(lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__4;
uint8_t l_Lean_Meta_Linear_isLinearTerm(lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__9;
uint8_t l_Lean_Meta_Linear_isLinearCnstr(lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__8;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LinearArith_Simp_0__Lean_Meta_Linear_parentIsTarget(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_Linear_isLinearTerm(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Meta_Linear_isLinearCnstr(x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 1;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LinearArith_Simp_0__Lean_Meta_Linear_parentIsTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_LinearArith_Simp_0__Lean_Meta_Linear_parentIsTarget(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Linear_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Linear_simp_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_simp_x3f___closed__2;
x_2 = l_Lean_Meta_Linear_simp_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Linear_simp_x3f___closed__4;
x_2 = l_Lean_Meta_Linear_simp_x3f___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arith expr: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Linear_simp_x3f___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Linear_simp_x3f___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_Linear_isLinearCnstr(x_1);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Meta_Linear_isLinearTerm(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l___private_Lean_Meta_Tactic_LinearArith_Simp_0__Lean_Meta_Linear_parentIsTarget(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_13 = l_Lean_Meta_Linear_simp_x3f___closed__6;
x_26 = lean_st_ref_get(x_6, x_7);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = 0;
x_14 = x_31;
x_15 = x_30;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_13, x_3, x_4, x_5, x_6, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_14 = x_36;
x_15 = x_35;
goto block_25;
}
block_25:
{
if (x_14 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Linear_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_Meta_Linear_simp_x3f___closed__8;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_Linear_simp_x3f___closed__10;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_13, x_21, x_3, x_4, x_5, x_6, x_15);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_Linear_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_23);
return x_24;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_2);
x_39 = l_Lean_Meta_Linear_Nat_simpCnstr_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Linear_simp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_LinearArith_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_LinearArith_Nat_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_LinearArith_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_LinearArith_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_LinearArith_Nat_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Linear_simp_x3f___closed__1 = _init_l_Lean_Meta_Linear_simp_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__1);
l_Lean_Meta_Linear_simp_x3f___closed__2 = _init_l_Lean_Meta_Linear_simp_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__2);
l_Lean_Meta_Linear_simp_x3f___closed__3 = _init_l_Lean_Meta_Linear_simp_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__3);
l_Lean_Meta_Linear_simp_x3f___closed__4 = _init_l_Lean_Meta_Linear_simp_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__4);
l_Lean_Meta_Linear_simp_x3f___closed__5 = _init_l_Lean_Meta_Linear_simp_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__5);
l_Lean_Meta_Linear_simp_x3f___closed__6 = _init_l_Lean_Meta_Linear_simp_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__6);
l_Lean_Meta_Linear_simp_x3f___closed__7 = _init_l_Lean_Meta_Linear_simp_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__7);
l_Lean_Meta_Linear_simp_x3f___closed__8 = _init_l_Lean_Meta_Linear_simp_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__8);
l_Lean_Meta_Linear_simp_x3f___closed__9 = _init_l_Lean_Meta_Linear_simp_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__9);
l_Lean_Meta_Linear_simp_x3f___closed__10 = _init_l_Lean_Meta_Linear_simp_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Linear_simp_x3f___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
