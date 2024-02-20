// Lean compiler output
// Module: Lean.Meta.Tactic.LinearArith.Simp
// Imports: Lean.Meta.Tactic.LinearArith.Basic Lean.Meta.Tactic.LinearArith.Nat.Simp
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
uint8_t l_Lean_Meta_Linear_isLinearCnstr(lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__7;
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_parentIsTarget___boxed(lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Linear_parentIsTarget(lean_object*);
lean_object* l_Lean_Meta_Linear_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__8;
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__4;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Meta_Linear_isLinearTerm(lean_object*);
lean_object* l_Lean_Meta_Linear_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Linear_simp_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Linear_parentIsTarget(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Linear_parentIsTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Linear_parentIsTarget(x_1);
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
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Linear_simp_x3f___closed__1;
x_2 = l_Lean_Meta_Linear_simp_x3f___closed__2;
x_3 = l_Lean_Meta_Linear_simp_x3f___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("arith expr: ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Linear_simp_x3f___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Linear_simp_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
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
x_12 = l_Lean_Meta_Linear_parentIsTarget(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Meta_Linear_simp_x3f___closed__4;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_Linear_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
lean_inc(x_1);
x_20 = l_Lean_MessageData_ofExpr(x_1);
x_21 = l_Lean_Meta_Linear_simp_x3f___closed__6;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_Linear_simp_x3f___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_13, x_24, x_3, x_4, x_5, x_6, x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Meta_Linear_Nat_simpExpr_x3f(x_1, x_3, x_4, x_5, x_6, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_2);
x_30 = l_Lean_Meta_Linear_Nat_simpCnstr_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
return x_30;
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
lean_object* initialize_Lean_Meta_Tactic_LinearArith_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_LinearArith_Nat_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_LinearArith_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
