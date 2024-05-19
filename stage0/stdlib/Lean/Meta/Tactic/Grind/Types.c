// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Types
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Util
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static size_t l_Lean_Meta_Grind_instInhabitedGoal___closed__3;
static lean_object* l_Lean_Meta_Grind_instInhabitedGoal___closed__5;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Goal_clauses___default___closed__1;
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedClause___closed__1;
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedGoal___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_admit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Goal_clauses___default___closed__2;
static lean_object* l_Lean_Meta_Grind_instInhabitedGoal___closed__2;
static lean_object* l_Lean_Meta_Grind_Goal_clauses___default___closed__3;
static lean_object* l_Lean_Meta_Grind_instInhabitedClause___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_clauses___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedClause;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInputClause(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedGoal___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInputClause___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedGoal;
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedClause___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedClause___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedClause___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedClause() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedClause___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInputClause(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_FVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Expr_fvar___override(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Lean_Expr_fvar___override(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInputClause___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_mkInputClause(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_clauses___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_clauses___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Goal_clauses___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_clauses___default___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Grind_Goal_clauses___default___closed__2;
x_3 = l_Lean_Meta_Grind_Goal_clauses___default___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Goal_clauses___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Goal_clauses___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoal___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoal___closed__2;
x_2 = l_Lean_Meta_Grind_instInhabitedGoal___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_instInhabitedGoal___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedGoal___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedGoal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoal___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGoal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Goal_clauses___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Goal_admit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = 1;
x_9 = l_Lean_MVarId_admit(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedClause___closed__1 = _init_l_Lean_Meta_Grind_instInhabitedClause___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedClause___closed__1);
l_Lean_Meta_Grind_instInhabitedClause___closed__2 = _init_l_Lean_Meta_Grind_instInhabitedClause___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedClause___closed__2);
l_Lean_Meta_Grind_instInhabitedClause = _init_l_Lean_Meta_Grind_instInhabitedClause();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedClause);
l_Lean_Meta_Grind_Goal_clauses___default___closed__1 = _init_l_Lean_Meta_Grind_Goal_clauses___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Goal_clauses___default___closed__1);
l_Lean_Meta_Grind_Goal_clauses___default___closed__2 = _init_l_Lean_Meta_Grind_Goal_clauses___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Goal_clauses___default___closed__2);
l_Lean_Meta_Grind_Goal_clauses___default___closed__3 = _init_l_Lean_Meta_Grind_Goal_clauses___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Goal_clauses___default___closed__3);
l_Lean_Meta_Grind_Goal_clauses___default = _init_l_Lean_Meta_Grind_Goal_clauses___default();
lean_mark_persistent(l_Lean_Meta_Grind_Goal_clauses___default);
l_Lean_Meta_Grind_instInhabitedGoal___closed__1 = _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedGoal___closed__1);
l_Lean_Meta_Grind_instInhabitedGoal___closed__2 = _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedGoal___closed__2);
l_Lean_Meta_Grind_instInhabitedGoal___closed__3 = _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__3();
l_Lean_Meta_Grind_instInhabitedGoal___closed__4 = _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedGoal___closed__4);
l_Lean_Meta_Grind_instInhabitedGoal___closed__5 = _init_l_Lean_Meta_Grind_instInhabitedGoal___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedGoal___closed__5);
l_Lean_Meta_Grind_instInhabitedGoal = _init_l_Lean_Meta_Grind_instInhabitedGoal();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedGoal);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
