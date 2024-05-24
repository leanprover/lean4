// Lean compiler output
// Module: Lean.Meta.Tactic.FVarSubst
// Imports: Init Lean.Data.AssocList Lean.Expr Lean.LocalContext Lean.Util.ReplaceExpr
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_erase(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_Cache_new;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AssocList_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_map___default;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedFVarSubst;
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_empty;
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AssocList_mapVal___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_AssocList_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_applyFVarSubst(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_FVarSubst_map___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_262; lean_object* x_268; size_t x_269; uint8_t x_270; 
x_4 = lean_ptr_addr(x_2);
x_5 = 8191;
x_6 = lean_usize_mod(x_4, x_5);
x_268 = lean_array_uget(x_3, x_6);
x_269 = lean_ptr_addr(x_268);
lean_dec(x_268);
x_270 = lean_usize_dec_eq(x_4, x_269);
if (x_270 == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_2, 0);
lean_inc(x_271);
x_272 = l_Lean_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_271, x_1);
lean_dec(x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_inc(x_2);
x_262 = x_2;
goto block_267;
}
else
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec(x_272);
x_262 = x_273;
goto block_267;
}
}
else
{
lean_object* x_274; 
x_274 = lean_box(0);
x_7 = x_274;
goto block_261;
}
}
else
{
size_t x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_2);
x_275 = lean_usize_add(x_6, x_5);
x_276 = lean_array_uget(x_3, x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_3);
return x_277;
}
block_261:
{
lean_dec(x_7);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_8, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_9);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_2);
x_17 = lean_array_uset(x_16, x_6, x_2);
x_18 = lean_usize_add(x_6, x_5);
x_19 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_20 = lean_ptr_addr(x_11);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_2);
x_22 = l_Lean_Expr_app___override(x_11, x_15);
lean_inc(x_22);
x_23 = lean_array_uset(x_17, x_18, x_22);
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_25 = lean_ptr_addr(x_15);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_27 = l_Lean_Expr_app___override(x_11, x_15);
lean_inc(x_27);
x_28 = lean_array_uset(x_17, x_18, x_27);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
else
{
lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_2);
x_29 = lean_array_uset(x_17, x_18, x_2);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
lean_inc(x_2);
x_32 = lean_array_uset(x_31, x_6, x_2);
x_33 = lean_usize_add(x_6, x_5);
x_34 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_35 = lean_ptr_addr(x_11);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_2);
x_37 = l_Lean_Expr_app___override(x_11, x_30);
lean_inc(x_37);
x_38 = lean_array_uset(x_32, x_33, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_41 = lean_ptr_addr(x_30);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = l_Lean_Expr_app___override(x_11, x_30);
lean_inc(x_43);
x_44 = lean_array_uset(x_32, x_33, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_11);
lean_inc(x_2);
x_46 = lean_array_uset(x_32, x_33, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_49);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_49, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_50, x_54);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; size_t x_62; size_t x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_array_uset(x_58, x_6, x_2);
x_60 = lean_usize_add(x_6, x_5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_61 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_62 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_63 = lean_ptr_addr(x_53);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_50);
x_65 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_65);
x_66 = lean_array_uset(x_59, x_60, x_65);
lean_ctor_set(x_55, 1, x_66);
lean_ctor_set(x_55, 0, x_65);
return x_55;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_68 = lean_ptr_addr(x_57);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_70 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_70);
x_71 = lean_array_uset(x_59, x_60, x_70);
lean_ctor_set(x_55, 1, x_71);
lean_ctor_set(x_55, 0, x_70);
return x_55;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_51, x_51);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
x_73 = l_Lean_Expr_lam___override(x_48, x_53, x_57, x_51);
lean_inc(x_73);
x_74 = lean_array_uset(x_59, x_60, x_73);
lean_ctor_set(x_55, 1, x_74);
lean_ctor_set(x_55, 0, x_73);
return x_55;
}
else
{
lean_object* x_75; 
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_61);
x_75 = lean_array_uset(x_59, x_60, x_61);
lean_ctor_set(x_55, 1, x_75);
lean_ctor_set(x_55, 0, x_61);
return x_55;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; size_t x_79; lean_object* x_80; size_t x_81; size_t x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_55, 0);
x_77 = lean_ctor_get(x_55, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_55);
x_78 = lean_array_uset(x_77, x_6, x_2);
x_79 = lean_usize_add(x_6, x_5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
x_80 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_81 = lean_ptr_addr(x_49);
lean_dec(x_49);
x_82 = lean_ptr_addr(x_53);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_50);
x_84 = l_Lean_Expr_lam___override(x_48, x_53, x_76, x_51);
lean_inc(x_84);
x_85 = lean_array_uset(x_78, x_79, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
size_t x_87; size_t x_88; uint8_t x_89; 
x_87 = lean_ptr_addr(x_50);
lean_dec(x_50);
x_88 = lean_ptr_addr(x_76);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_80);
x_90 = l_Lean_Expr_lam___override(x_48, x_53, x_76, x_51);
lean_inc(x_90);
x_91 = lean_array_uset(x_78, x_79, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_51, x_51);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_80);
x_94 = l_Lean_Expr_lam___override(x_48, x_53, x_76, x_51);
lean_inc(x_94);
x_95 = lean_array_uset(x_78, x_79, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_76);
lean_dec(x_53);
lean_dec(x_48);
lean_inc(x_80);
x_97 = lean_array_uset(x_78, x_79, x_80);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_80);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_99 = lean_ctor_get(x_2, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_100);
x_103 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_100, x_3);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_101);
x_106 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_101, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; lean_object* x_112; size_t x_113; size_t x_114; uint8_t x_115; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
x_110 = lean_array_uset(x_109, x_6, x_2);
x_111 = lean_usize_add(x_6, x_5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_112 = l_Lean_Expr_forallE___override(x_99, x_100, x_101, x_102);
x_113 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_114 = lean_ptr_addr(x_104);
x_115 = lean_usize_dec_eq(x_113, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
lean_dec(x_101);
x_116 = l_Lean_Expr_forallE___override(x_99, x_104, x_108, x_102);
lean_inc(x_116);
x_117 = lean_array_uset(x_110, x_111, x_116);
lean_ctor_set(x_106, 1, x_117);
lean_ctor_set(x_106, 0, x_116);
return x_106;
}
else
{
size_t x_118; size_t x_119; uint8_t x_120; 
x_118 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_119 = lean_ptr_addr(x_108);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_112);
x_121 = l_Lean_Expr_forallE___override(x_99, x_104, x_108, x_102);
lean_inc(x_121);
x_122 = lean_array_uset(x_110, x_111, x_121);
lean_ctor_set(x_106, 1, x_122);
lean_ctor_set(x_106, 0, x_121);
return x_106;
}
else
{
uint8_t x_123; 
x_123 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_102, x_102);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_112);
x_124 = l_Lean_Expr_forallE___override(x_99, x_104, x_108, x_102);
lean_inc(x_124);
x_125 = lean_array_uset(x_110, x_111, x_124);
lean_ctor_set(x_106, 1, x_125);
lean_ctor_set(x_106, 0, x_124);
return x_106;
}
else
{
lean_object* x_126; 
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_99);
lean_inc(x_112);
x_126 = lean_array_uset(x_110, x_111, x_112);
lean_ctor_set(x_106, 1, x_126);
lean_ctor_set(x_106, 0, x_112);
return x_106;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; size_t x_130; lean_object* x_131; size_t x_132; size_t x_133; uint8_t x_134; 
x_127 = lean_ctor_get(x_106, 0);
x_128 = lean_ctor_get(x_106, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_106);
x_129 = lean_array_uset(x_128, x_6, x_2);
x_130 = lean_usize_add(x_6, x_5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_131 = l_Lean_Expr_forallE___override(x_99, x_100, x_101, x_102);
x_132 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_133 = lean_ptr_addr(x_104);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_131);
lean_dec(x_101);
x_135 = l_Lean_Expr_forallE___override(x_99, x_104, x_127, x_102);
lean_inc(x_135);
x_136 = lean_array_uset(x_129, x_130, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
else
{
size_t x_138; size_t x_139; uint8_t x_140; 
x_138 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_139 = lean_ptr_addr(x_127);
x_140 = lean_usize_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_131);
x_141 = l_Lean_Expr_forallE___override(x_99, x_104, x_127, x_102);
lean_inc(x_141);
x_142 = lean_array_uset(x_129, x_130, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
else
{
uint8_t x_144; 
x_144 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_102, x_102);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_131);
x_145 = l_Lean_Expr_forallE___override(x_99, x_104, x_127, x_102);
lean_inc(x_145);
x_146 = lean_array_uset(x_129, x_130, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
lean_dec(x_104);
lean_dec(x_99);
lean_inc(x_131);
x_148 = lean_array_uset(x_129, x_130, x_131);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_131);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
}
case 8:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_150 = lean_ctor_get(x_2, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 3);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_151);
x_155 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_151, x_3);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_152);
x_158 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_152, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_153);
x_161 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_153, x_160);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; size_t x_168; uint8_t x_169; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_2);
x_165 = lean_array_uset(x_164, x_6, x_2);
x_166 = lean_usize_add(x_6, x_5);
x_167 = lean_ptr_addr(x_151);
lean_dec(x_151);
x_168 = lean_ptr_addr(x_156);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_2);
x_170 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_163, x_154);
lean_inc(x_170);
x_171 = lean_array_uset(x_165, x_166, x_170);
lean_ctor_set(x_161, 1, x_171);
lean_ctor_set(x_161, 0, x_170);
return x_161;
}
else
{
size_t x_172; size_t x_173; uint8_t x_174; 
x_172 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_173 = lean_ptr_addr(x_159);
x_174 = lean_usize_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_153);
lean_dec(x_2);
x_175 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_163, x_154);
lean_inc(x_175);
x_176 = lean_array_uset(x_165, x_166, x_175);
lean_ctor_set(x_161, 1, x_176);
lean_ctor_set(x_161, 0, x_175);
return x_161;
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_178 = lean_ptr_addr(x_163);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_2);
x_180 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_163, x_154);
lean_inc(x_180);
x_181 = lean_array_uset(x_165, x_166, x_180);
lean_ctor_set(x_161, 1, x_181);
lean_ctor_set(x_161, 0, x_180);
return x_161;
}
else
{
lean_object* x_182; 
lean_dec(x_163);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_150);
lean_inc(x_2);
x_182 = lean_array_uset(x_165, x_166, x_2);
lean_ctor_set(x_161, 1, x_182);
lean_ctor_set(x_161, 0, x_2);
return x_161;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; size_t x_188; uint8_t x_189; 
x_183 = lean_ctor_get(x_161, 0);
x_184 = lean_ctor_get(x_161, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_161);
lean_inc(x_2);
x_185 = lean_array_uset(x_184, x_6, x_2);
x_186 = lean_usize_add(x_6, x_5);
x_187 = lean_ptr_addr(x_151);
lean_dec(x_151);
x_188 = lean_ptr_addr(x_156);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_2);
x_190 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_183, x_154);
lean_inc(x_190);
x_191 = lean_array_uset(x_185, x_186, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
else
{
size_t x_193; size_t x_194; uint8_t x_195; 
x_193 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_194 = lean_ptr_addr(x_159);
x_195 = lean_usize_dec_eq(x_193, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_153);
lean_dec(x_2);
x_196 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_183, x_154);
lean_inc(x_196);
x_197 = lean_array_uset(x_185, x_186, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
else
{
size_t x_199; size_t x_200; uint8_t x_201; 
x_199 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_200 = lean_ptr_addr(x_183);
x_201 = lean_usize_dec_eq(x_199, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_2);
x_202 = l_Lean_Expr_letE___override(x_150, x_156, x_159, x_183, x_154);
lean_inc(x_202);
x_203 = lean_array_uset(x_185, x_186, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_183);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_150);
lean_inc(x_2);
x_205 = lean_array_uset(x_185, x_186, x_2);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_2);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
}
case 10:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_2, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_2, 1);
lean_inc(x_208);
lean_inc(x_208);
x_209 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_208, x_3);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; size_t x_215; size_t x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_2);
x_213 = lean_array_uset(x_212, x_6, x_2);
x_214 = lean_usize_add(x_6, x_5);
x_215 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_216 = lean_ptr_addr(x_211);
x_217 = lean_usize_dec_eq(x_215, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_2);
x_218 = l_Lean_Expr_mdata___override(x_207, x_211);
lean_inc(x_218);
x_219 = lean_array_uset(x_213, x_214, x_218);
lean_ctor_set(x_209, 1, x_219);
lean_ctor_set(x_209, 0, x_218);
return x_209;
}
else
{
lean_object* x_220; 
lean_dec(x_211);
lean_dec(x_207);
lean_inc(x_2);
x_220 = lean_array_uset(x_213, x_214, x_2);
lean_ctor_set(x_209, 1, x_220);
lean_ctor_set(x_209, 0, x_2);
return x_209;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; size_t x_224; size_t x_225; size_t x_226; uint8_t x_227; 
x_221 = lean_ctor_get(x_209, 0);
x_222 = lean_ctor_get(x_209, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_209);
lean_inc(x_2);
x_223 = lean_array_uset(x_222, x_6, x_2);
x_224 = lean_usize_add(x_6, x_5);
x_225 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_226 = lean_ptr_addr(x_221);
x_227 = lean_usize_dec_eq(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_2);
x_228 = l_Lean_Expr_mdata___override(x_207, x_221);
lean_inc(x_228);
x_229 = lean_array_uset(x_223, x_224, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_221);
lean_dec(x_207);
lean_inc(x_2);
x_231 = lean_array_uset(x_223, x_224, x_2);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 11:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_233 = lean_ctor_get(x_2, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_2, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_2, 2);
lean_inc(x_235);
lean_inc(x_235);
x_236 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_235, x_3);
x_237 = !lean_is_exclusive(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; size_t x_241; size_t x_242; size_t x_243; uint8_t x_244; 
x_238 = lean_ctor_get(x_236, 0);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_2);
x_240 = lean_array_uset(x_239, x_6, x_2);
x_241 = lean_usize_add(x_6, x_5);
x_242 = lean_ptr_addr(x_235);
lean_dec(x_235);
x_243 = lean_ptr_addr(x_238);
x_244 = lean_usize_dec_eq(x_242, x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_2);
x_245 = l_Lean_Expr_proj___override(x_233, x_234, x_238);
lean_inc(x_245);
x_246 = lean_array_uset(x_240, x_241, x_245);
lean_ctor_set(x_236, 1, x_246);
lean_ctor_set(x_236, 0, x_245);
return x_236;
}
else
{
lean_object* x_247; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec(x_233);
lean_inc(x_2);
x_247 = lean_array_uset(x_240, x_241, x_2);
lean_ctor_set(x_236, 1, x_247);
lean_ctor_set(x_236, 0, x_2);
return x_236;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; size_t x_251; size_t x_252; size_t x_253; uint8_t x_254; 
x_248 = lean_ctor_get(x_236, 0);
x_249 = lean_ctor_get(x_236, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_236);
lean_inc(x_2);
x_250 = lean_array_uset(x_249, x_6, x_2);
x_251 = lean_usize_add(x_6, x_5);
x_252 = lean_ptr_addr(x_235);
lean_dec(x_235);
x_253 = lean_ptr_addr(x_248);
x_254 = lean_usize_dec_eq(x_252, x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_2);
x_255 = l_Lean_Expr_proj___override(x_233, x_234, x_248);
lean_inc(x_255);
x_256 = lean_array_uset(x_250, x_251, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_248);
lean_dec(x_234);
lean_dec(x_233);
lean_inc(x_2);
x_258 = lean_array_uset(x_250, x_251, x_2);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_2);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
default: 
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_2);
lean_ctor_set(x_260, 1, x_3);
return x_260;
}
}
}
block_267:
{
lean_object* x_263; size_t x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_array_uset(x_3, x_6, x_2);
x_264 = lean_usize_add(x_6, x_5);
lean_inc(x_262);
x_265 = lean_array_uset(x_263, x_264, x_262);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_262);
lean_ctor_set(x_266, 1, x_265);
return x_266;
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
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_ReplaceImpl_Cache_new;
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply(x_1, x_2);
lean_dec(x_1);
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
lean_dec(x_1);
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
x_17 = l_Lean_Meta_FVarSubst_apply(x_1, x_15);
x_18 = l_Lean_Meta_FVarSubst_apply(x_1, x_16);
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
x_26 = l_Lean_Meta_FVarSubst_apply(x_1, x_22);
x_27 = l_Lean_Meta_FVarSubst_apply(x_1, x_23);
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
LEAN_EXPORT lean_object* l_Lean_LocalDecl_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LocalContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Meta_FVarSubst_map___default = _init_l_Lean_Meta_FVarSubst_map___default();
lean_mark_persistent(l_Lean_Meta_FVarSubst_map___default);
l_Lean_Meta_instInhabitedFVarSubst = _init_l_Lean_Meta_instInhabitedFVarSubst();
lean_mark_persistent(l_Lean_Meta_instInhabitedFVarSubst);
l_Lean_Meta_FVarSubst_empty = _init_l_Lean_Meta_FVarSubst_empty();
lean_mark_persistent(l_Lean_Meta_FVarSubst_empty);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
