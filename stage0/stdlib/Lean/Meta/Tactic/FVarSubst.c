// Lean compiler output
// Module: Lean.Meta.Tactic.FVarSubst
// Imports: Init Std.Data.AssocList Lean.Expr Lean.LocalContext Lean.Util.ReplaceExpr
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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_erase(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Meta_FVarSubst_any(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4;
lean_object* l_Lean_LocalDecl_applyFVarSubst_match__1(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
uint8_t l_Std_AssocList_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Meta_FVarSubst_contains(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_map___default;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
uint8_t l_Std_AssocList_any___rarg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply_match__2(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_LocalDecl_applyFVarSubst_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_empty;
lean_object* l_Lean_Meta_FVarSubst_apply_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1;
lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_AssocList_mapVal___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get_match__1(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply_match__1(lean_object*);
uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object*);
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Lean_Expr_applyFVarSubst(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_FVarSubst_map___default() {
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
uint8_t l_Lean_Meta_FVarSubst_isEmpty(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Std_AssocList_isEmpty___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_FVarSubst_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_FVarSubst_isEmpty(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_Lean_Meta_FVarSubst_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_FVarSubst_contains___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVarId(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_AssocList_contains___at_Lean_Meta_FVarSubst_contains___spec__1(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_insert___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Std_AssocList_mapVal___rarg(x_5, x_1);
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
lean_object* l_Lean_Meta_FVarSubst_insert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_FVarSubst_insert___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_1, x_7);
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
x_14 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_1, x_12);
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
lean_object* l_Lean_Meta_FVarSubst_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_erase___at_Lean_Meta_FVarSubst_erase___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_erase___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_erase(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_FVarSubst_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_find_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_find_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_get_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_FVarSubst_get_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_get_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_FVarSubst_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_mkFVar(x_2);
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
lean_object* l_Lean_Meta_FVarSubst_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_apply_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_FVarSubst_apply_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_apply_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_FVarSubst_apply_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Meta_FVarSubst_apply_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_FVarSubst_apply_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_237; lean_object* x_238; lean_object* x_245; size_t x_246; uint8_t x_247; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_237 = lean_ctor_get(x_4, 0);
lean_inc(x_237);
x_245 = lean_array_uget(x_237, x_6);
x_246 = lean_ptr_addr(x_245);
lean_dec(x_245);
x_247 = x_246 == x_5;
if (x_247 == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_3, 0);
lean_inc(x_248);
x_249 = l_Std_AssocList_find_x3f___at_Lean_Meta_FVarSubst_find_x3f___spec__1(x_248, x_1);
lean_dec(x_248);
if (lean_obj_tag(x_249) == 0)
{
lean_inc(x_3);
x_238 = x_3;
goto block_244;
}
else
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec(x_249);
x_238 = x_250;
goto block_244;
}
}
else
{
lean_object* x_251; 
lean_dec(x_237);
x_251 = lean_box(0);
x_7 = x_251;
goto block_236;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_237);
lean_dec(x_3);
x_252 = lean_ctor_get(x_4, 1);
lean_inc(x_252);
x_253 = lean_array_uget(x_252, x_6);
lean_dec(x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_4);
return x_254;
}
block_236:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_8);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_8, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_3);
x_19 = lean_array_uset(x_18, x_6, x_3);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_expr_update_app(x_3, x_12, x_16);
lean_inc(x_24);
x_25 = lean_array_uset(x_23, x_6, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_14, 1, x_26);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_10);
x_29 = lean_expr_update_app(x_28, x_12, x_16);
lean_inc(x_29);
x_30 = lean_array_uset(x_27, x_6, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_inc(x_3);
x_35 = lean_array_uset(x_34, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_36 = x_3;
} else {
 lean_dec_ref(x_3);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(5, 2, 8);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_10);
x_39 = lean_expr_update_app(x_38, x_12, x_32);
lean_inc(x_39);
x_40 = lean_array_uset(x_37, x_6, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 6:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_44);
x_47 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_44, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_45);
x_50 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_45, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_inc(x_3);
x_55 = lean_array_uset(x_54, x_6, x_3);
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_3, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_3, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_3, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_dec(x_53);
x_61 = (uint8_t)((x_46 << 24) >> 61);
x_62 = lean_expr_update_lambda(x_3, x_61, x_48, x_52);
lean_inc(x_62);
x_63 = lean_array_uset(x_60, x_6, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_50, 1, x_64);
lean_ctor_set(x_50, 0, x_62);
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_3);
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_44);
lean_ctor_set(x_66, 2, x_45);
lean_ctor_set_uint64(x_66, sizeof(void*)*3, x_46);
x_67 = (uint8_t)((x_46 << 24) >> 61);
x_68 = lean_expr_update_lambda(x_66, x_67, x_48, x_52);
lean_inc(x_68);
x_69 = lean_array_uset(x_65, x_6, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_50, 1, x_70);
lean_ctor_set(x_50, 0, x_68);
return x_50;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_71 = lean_ctor_get(x_50, 0);
x_72 = lean_ctor_get(x_50, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_50);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_inc(x_3);
x_74 = lean_array_uset(x_73, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_75 = x_3;
} else {
 lean_dec_ref(x_3);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(6, 3, 8);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_43);
lean_ctor_set(x_77, 1, x_44);
lean_ctor_set(x_77, 2, x_45);
lean_ctor_set_uint64(x_77, sizeof(void*)*3, x_46);
x_78 = (uint8_t)((x_46 << 24) >> 61);
x_79 = lean_expr_update_lambda(x_77, x_78, x_48, x_71);
lean_inc(x_79);
x_80 = lean_array_uset(x_76, x_6, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
case 7:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 2);
lean_inc(x_85);
x_86 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_84);
x_87 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_84, x_4);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_85);
x_90 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_85, x_89);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_inc(x_3);
x_95 = lean_array_uset(x_94, x_6, x_3);
x_96 = !lean_is_exclusive(x_3);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_3, 2);
lean_dec(x_97);
x_98 = lean_ctor_get(x_3, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_3, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_101 = (uint8_t)((x_86 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_88, x_92);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_6, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_90, 1, x_104);
lean_ctor_set(x_90, 0, x_102);
return x_90;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_105 = lean_ctor_get(x_93, 1);
lean_inc(x_105);
lean_dec(x_93);
x_106 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_106, 0, x_83);
lean_ctor_set(x_106, 1, x_84);
lean_ctor_set(x_106, 2, x_85);
lean_ctor_set_uint64(x_106, sizeof(void*)*3, x_86);
x_107 = (uint8_t)((x_86 << 24) >> 61);
x_108 = lean_expr_update_forall(x_106, x_107, x_88, x_92);
lean_inc(x_108);
x_109 = lean_array_uset(x_105, x_6, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_90, 1, x_110);
lean_ctor_set(x_90, 0, x_108);
return x_90;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_90, 0);
x_112 = lean_ctor_get(x_90, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_90);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_inc(x_3);
x_114 = lean_array_uset(x_113, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_115 = x_3;
} else {
 lean_dec_ref(x_3);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(7, 3, 8);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_83);
lean_ctor_set(x_117, 1, x_84);
lean_ctor_set(x_117, 2, x_85);
lean_ctor_set_uint64(x_117, sizeof(void*)*3, x_86);
x_118 = (uint8_t)((x_86 << 24) >> 61);
x_119 = lean_expr_update_forall(x_117, x_118, x_88, x_111);
lean_inc(x_119);
x_120 = lean_array_uset(x_116, x_6, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
case 8:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint64_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_123 = lean_ctor_get(x_3, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_3, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_3, 3);
lean_inc(x_126);
x_127 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_124);
x_128 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_124, x_4);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_125);
x_131 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_125, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_126);
x_134 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_126, x_133);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_134, 1);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_inc(x_3);
x_139 = lean_array_uset(x_138, x_6, x_3);
x_140 = !lean_is_exclusive(x_3);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_3, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_3, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_3, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_3, 0);
lean_dec(x_144);
x_145 = lean_ctor_get(x_137, 1);
lean_inc(x_145);
lean_dec(x_137);
x_146 = lean_expr_update_let(x_3, x_129, x_132, x_136);
lean_inc(x_146);
x_147 = lean_array_uset(x_145, x_6, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_134, 1, x_148);
lean_ctor_set(x_134, 0, x_146);
return x_134;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_3);
x_149 = lean_ctor_get(x_137, 1);
lean_inc(x_149);
lean_dec(x_137);
x_150 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_150, 0, x_123);
lean_ctor_set(x_150, 1, x_124);
lean_ctor_set(x_150, 2, x_125);
lean_ctor_set(x_150, 3, x_126);
lean_ctor_set_uint64(x_150, sizeof(void*)*4, x_127);
x_151 = lean_expr_update_let(x_150, x_129, x_132, x_136);
lean_inc(x_151);
x_152 = lean_array_uset(x_149, x_6, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_139);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_134, 1, x_153);
lean_ctor_set(x_134, 0, x_151);
return x_134;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_134, 0);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_134);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_inc(x_3);
x_157 = lean_array_uset(x_156, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_158 = x_3;
} else {
 lean_dec_ref(x_3);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(8, 4, 8);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_123);
lean_ctor_set(x_160, 1, x_124);
lean_ctor_set(x_160, 2, x_125);
lean_ctor_set(x_160, 3, x_126);
lean_ctor_set_uint64(x_160, sizeof(void*)*4, x_127);
x_161 = lean_expr_update_let(x_160, x_129, x_132, x_154);
lean_inc(x_161);
x_162 = lean_array_uset(x_159, x_6, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_157);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
case 10:
{
lean_object* x_165; lean_object* x_166; uint64_t x_167; lean_object* x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_3, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_3, 1);
lean_inc(x_166);
x_167 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_166);
x_168 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_166, x_4);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_inc(x_3);
x_173 = lean_array_uset(x_172, x_6, x_3);
x_174 = !lean_is_exclusive(x_3);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_3, 1);
lean_dec(x_175);
x_176 = lean_ctor_get(x_3, 0);
lean_dec(x_176);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
x_178 = lean_expr_update_mdata(x_3, x_170);
lean_inc(x_178);
x_179 = lean_array_uset(x_177, x_6, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set(x_168, 1, x_180);
lean_ctor_set(x_168, 0, x_178);
return x_168;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_3);
x_181 = lean_ctor_get(x_171, 1);
lean_inc(x_181);
lean_dec(x_171);
x_182 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_182, 0, x_165);
lean_ctor_set(x_182, 1, x_166);
lean_ctor_set_uint64(x_182, sizeof(void*)*2, x_167);
x_183 = lean_expr_update_mdata(x_182, x_170);
lean_inc(x_183);
x_184 = lean_array_uset(x_181, x_6, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_173);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_168, 1, x_185);
lean_ctor_set(x_168, 0, x_183);
return x_168;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_ctor_get(x_168, 0);
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_168);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_inc(x_3);
x_189 = lean_array_uset(x_188, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_190 = x_3;
} else {
 lean_dec_ref(x_3);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(10, 2, 8);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_165);
lean_ctor_set(x_192, 1, x_166);
lean_ctor_set_uint64(x_192, sizeof(void*)*2, x_167);
x_193 = lean_expr_update_mdata(x_192, x_186);
lean_inc(x_193);
x_194 = lean_array_uset(x_191, x_6, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
case 11:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_3, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_3, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_3, 2);
lean_inc(x_199);
x_200 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_199);
x_201 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_2, x_199, x_4);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_inc(x_3);
x_206 = lean_array_uset(x_205, x_6, x_3);
x_207 = !lean_is_exclusive(x_3);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_3, 2);
lean_dec(x_208);
x_209 = lean_ctor_get(x_3, 1);
lean_dec(x_209);
x_210 = lean_ctor_get(x_3, 0);
lean_dec(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
x_212 = lean_expr_update_proj(x_3, x_203);
lean_inc(x_212);
x_213 = lean_array_uset(x_211, x_6, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_206);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_201, 1, x_214);
lean_ctor_set(x_201, 0, x_212);
return x_201;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_3);
x_215 = lean_ctor_get(x_204, 1);
lean_inc(x_215);
lean_dec(x_204);
x_216 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_216, 0, x_197);
lean_ctor_set(x_216, 1, x_198);
lean_ctor_set(x_216, 2, x_199);
lean_ctor_set_uint64(x_216, sizeof(void*)*3, x_200);
x_217 = lean_expr_update_proj(x_216, x_203);
lean_inc(x_217);
x_218 = lean_array_uset(x_215, x_6, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_206);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_201, 1, x_219);
lean_ctor_set(x_201, 0, x_217);
return x_201;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_220 = lean_ctor_get(x_201, 0);
x_221 = lean_ctor_get(x_201, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_201);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_inc(x_3);
x_223 = lean_array_uset(x_222, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_224 = x_3;
} else {
 lean_dec_ref(x_3);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(11, 3, 8);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_197);
lean_ctor_set(x_226, 1, x_198);
lean_ctor_set(x_226, 2, x_199);
lean_ctor_set_uint64(x_226, sizeof(void*)*3, x_200);
x_227 = lean_expr_update_proj(x_226, x_220);
lean_inc(x_227);
x_228 = lean_array_uset(x_225, x_6, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
case 12:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_3);
x_231 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1;
x_232 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4;
x_233 = lean_panic_fn(x_231, x_232);
x_234 = lean_apply_1(x_233, x_4);
return x_234;
}
default: 
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_3);
lean_ctor_set(x_235, 1, x_4);
return x_235;
}
}
}
block_244:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_array_uset(x_237, x_6, x_3);
x_240 = lean_ctor_get(x_4, 1);
lean_inc(x_240);
lean_dec(x_4);
lean_inc(x_238);
x_241 = lean_array_uset(x_240, x_6, x_238);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_238);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_AssocList_isEmpty___rarg(x_1);
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
size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 8192;
x_6 = l_Lean_Expr_ReplaceImpl_initCache;
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_5, x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Meta_FVarSubst_apply___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_FVarSubst_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_FVarSubst_domain(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Std_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___at_Lean_Meta_FVarSubst_domain___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_domain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_FVarSubst_domain(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Meta_FVarSubst_any(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_AssocList_any___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_FVarSubst_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_FVarSubst_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_LocalDecl_applyFVarSubst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l_Lean_LocalDecl_applyFVarSubst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LocalDecl_applyFVarSubst_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_LocalDecl_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_11 = l_Lean_Meta_FVarSubst_apply(x_1, x_9);
x_12 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = l_Lean_Meta_FVarSubst_apply(x_1, x_14);
x_17 = l_Lean_Meta_FVarSubst_apply(x_1, x_15);
lean_ctor_set(x_2, 4, x_17);
lean_ctor_set(x_2, 3, x_16);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_24 = l_Lean_Meta_FVarSubst_apply(x_1, x_21);
x_25 = l_Lean_Meta_FVarSubst_apply(x_1, x_22);
x_26 = lean_alloc_ctor(1, 5, 1);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_23);
return x_26;
}
}
}
}
lean_object* l_Lean_LocalDecl_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LocalDecl_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_applyFVarSubst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_FVarSubst_apply(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_applyFVarSubst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_applyFVarSubst(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_Data_AssocList(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_LocalContext(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_AssocList(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_FVarSubst_map___default = _init_l_Lean_Meta_FVarSubst_map___default();
lean_mark_persistent(l_Lean_Meta_FVarSubst_map___default);
l_Lean_Meta_FVarSubst_empty = _init_l_Lean_Meta_FVarSubst_empty();
lean_mark_persistent(l_Lean_Meta_FVarSubst_empty);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
