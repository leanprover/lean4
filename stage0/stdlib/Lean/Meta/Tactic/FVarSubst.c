// Lean compiler output
// Module: Lean.Meta.Tactic.FVarSubst
// Imports: Lean.Data.AssocList Lean.Expr Lean.LocalContext Lean.Util.ReplaceExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_empty;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_append___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object*, lean_object*);
uint8_t l_Lean_AssocList_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFVarSubst;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AssocList_mapVal___rarg(lean_object*, lean_object*);
uint8_t l_Lean_AssocList_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_contains(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedFVarSubst() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_FVarSubst_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_AssocList_isEmpty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_FVarSubst_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_FVarSubst_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVarId(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_insert___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_AssocList_mapVal___rarg(x_5, x_1);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_FVarSubst_insert___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_1, x_7);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_erase(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_find_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Expr_fvar___override(x_2);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_3, x_1);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_AssocList_isEmpty___rarg(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_2);
if (x_4 == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_apply___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_replace_expr(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_FVarSubst_domain(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_any(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_AssocList_any___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_FVarSubst_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_append___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_Lean_Meta_FVarSubst_apply(x_1, x_5);
lean_dec(x_5);
x_8 = l_Lean_Meta_FVarSubst_insert(x_2, x_4, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_append___spec__1(x_2, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_Lean_Meta_FVarSubst_apply(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 3, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_12 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*4 + 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 3);
x_16 = lean_ctor_get(x_2, 4);
lean_inc(x_1);
x_17 = l_Lean_Meta_FVarSubst_apply(x_1, x_15);
lean_dec(x_15);
x_18 = l_Lean_Meta_FVarSubst_apply(x_1, x_16);
lean_dec(x_16);
lean_ctor_set(x_2, 4, x_18);
lean_ctor_set(x_2, 3, x_17);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
x_26 = l_Lean_Meta_FVarSubst_apply(x_1, x_22);
lean_dec(x_22);
x_27 = l_Lean_Meta_FVarSubst_apply(x_1, x_23);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 5, 2);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 1, x_25);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_applyFVarSubst(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_AssocList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedFVarSubst = _init_l_Lean_Meta_instInhabitedFVarSubst();
lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst);
l_Lean_Meta_FVarSubst_empty = _init_l_Lean_Meta_FVarSubst_empty();
lean_mark_persistent(l_Lean_Meta_FVarSubst_empty);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
