// Lean compiler output
// Module: Lean.Util.FVarSubset
// Imports: Lean.Util.CollectFVars Lean.Util.FindExpr
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarsSubset___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarsSubset___closed__5;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
lean_object* lean_find_ext_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarsSubset___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Expr_fvarsSubset___closed__2;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Lean_Expr_fvarsSubset___closed__3;
static lean_object* l_Lean_Expr_fvarsSubset___closed__6;
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarsSubset___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; 
x_9 = l_Lean_Expr_hasFVar(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(2);
x_11 = lean_unbox(x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isFVar(x_2);
if (x_12 == 0)
{
x_3 = x_12;
goto block_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_Expr_fvarId_x21(x_2);
x_15 = l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg(x_13, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
x_3 = x_12;
goto block_8;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
block_8:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Expr_fvarsSubset___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_fvarsSubset___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_fvarsSubset___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_fvarsSubset___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_fvarsSubset___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Expr_fvarsSubset___closed__5;
x_2 = lean_box(0);
x_3 = l_Lean_Expr_fvarsSubset___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_fvarsSubset(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_2);
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Expr_hasFVar(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = lean_unbox(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Expr_fvarsSubset___closed__6;
x_10 = l_Lean_CollectFVars_main(x_2, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Expr_fvarsSubset___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_find_ext_expr(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_7;
}
else
{
uint8_t x_13; 
lean_dec(x_12);
x_13 = lean_unbox(x_6);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_Expr_fvarsSubset_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_fvarsSubset___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarsSubset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_fvarsSubset(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FVarSubset(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_fvarsSubset___closed__0 = _init_l_Lean_Expr_fvarsSubset___closed__0();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__0);
l_Lean_Expr_fvarsSubset___closed__1 = _init_l_Lean_Expr_fvarsSubset___closed__1();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__1);
l_Lean_Expr_fvarsSubset___closed__2 = _init_l_Lean_Expr_fvarsSubset___closed__2();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__2);
l_Lean_Expr_fvarsSubset___closed__3 = _init_l_Lean_Expr_fvarsSubset___closed__3();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__3);
l_Lean_Expr_fvarsSubset___closed__4 = _init_l_Lean_Expr_fvarsSubset___closed__4();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__4);
l_Lean_Expr_fvarsSubset___closed__5 = _init_l_Lean_Expr_fvarsSubset___closed__5();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__5);
l_Lean_Expr_fvarsSubset___closed__6 = _init_l_Lean_Expr_fvarsSubset___closed__6();
lean_mark_persistent(l_Lean_Expr_fvarsSubset___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
