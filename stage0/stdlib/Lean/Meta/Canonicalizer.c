// Lean compiler output
// Module: Lean.Meta.Canonicalizer
// Imports: Lean.Data.HashMap Lean.Util.ShareCommon Lean.Meta.Basic Lean.Meta.FunInfo Std.Data.HashMap.Raw
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__3(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Canonicalizer_canon_unsafe__1___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___lambda__1(lean_object*, uint64_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Canonicalizer_canon_unsafe__1___spec__1(uint64_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(uint64_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1;
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__3(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_canon___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__4___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__5(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__4___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__2(lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(lean_object*, uint64_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__4(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Canonicalizer_instBEqExprVisited(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Canonicalizer_instHashableExprVisited(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_mk_ref(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_2);
lean_inc(x_10);
x_13 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_15);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_mk_ref(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_box(x_2);
lean_inc(x_11);
x_14 = lean_apply_7(x_1, x_13, x_11, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_15);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_9, 1, x_20);
lean_ctor_set(x_9, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_9);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_box(x_2);
lean_inc(x_27);
x_30 = lean_apply_7(x_1, x_29, x_27, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_27, x_32);
lean_dec(x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Canonicalizer_CanonM_run___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_ptr_addr(x_1);
x_12 = lean_usize_to_uint64(x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_9, x_23);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___spec__1(x_1, x_24);
lean_dec(x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__4___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = lean_ptr_addr(x_23);
x_28 = lean_usize_to_uint64(x_27);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__4___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_ptr_addr(x_1);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_box_uint64(x_2);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_ptr_addr(x_1);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(x_1, x_2, x_16);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
x_22 = lean_box_uint64(x_2);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_16);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(lean_object* x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_19 = lean_st_ref_set(x_4, x_11, x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; uint8_t x_44; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
x_29 = lean_array_get_size(x_28);
x_30 = lean_ptr_addr(x_1);
x_31 = lean_usize_to_uint64(x_30);
x_32 = 32;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = 16;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_40 = 1;
x_41 = lean_usize_sub(x_39, x_40);
x_42 = lean_usize_land(x_38, x_41);
x_43 = lean_array_uget(x_28, x_42);
x_44 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1(x_1, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_27, x_45);
lean_dec(x_27);
x_47 = lean_box_uint64(x_2);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_43);
x_49 = lean_array_uset(x_28, x_42, x_48);
x_50 = lean_unsigned_to_nat(4u);
x_51 = lean_nat_mul(x_46, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_div(x_51, x_52);
lean_dec(x_51);
x_54 = lean_array_get_size(x_49);
x_55 = lean_nat_dec_le(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__2(x_49);
lean_ctor_set(x_14, 1, x_56);
lean_ctor_set(x_14, 0, x_46);
x_57 = lean_st_ref_set(x_4, x_11, x_12);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_ctor_set(x_14, 1, x_49);
lean_ctor_set(x_14, 0, x_46);
x_64 = lean_st_ref_set(x_4, x_11, x_12);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_box(0);
x_72 = lean_array_uset(x_28, x_42, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(x_1, x_2, x_43);
x_74 = lean_array_uset(x_72, x_42, x_73);
lean_ctor_set(x_14, 1, x_74);
x_75 = lean_st_ref_set(x_4, x_11, x_12);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; size_t x_93; size_t x_94; size_t x_95; size_t x_96; size_t x_97; lean_object* x_98; uint8_t x_99; 
x_82 = lean_ctor_get(x_14, 0);
x_83 = lean_ctor_get(x_14, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_14);
x_84 = lean_array_get_size(x_83);
x_85 = lean_ptr_addr(x_1);
x_86 = lean_usize_to_uint64(x_85);
x_87 = 32;
x_88 = lean_uint64_shift_right(x_86, x_87);
x_89 = lean_uint64_xor(x_86, x_88);
x_90 = 16;
x_91 = lean_uint64_shift_right(x_89, x_90);
x_92 = lean_uint64_xor(x_89, x_91);
x_93 = lean_uint64_to_usize(x_92);
x_94 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_95 = 1;
x_96 = lean_usize_sub(x_94, x_95);
x_97 = lean_usize_land(x_93, x_96);
x_98 = lean_array_uget(x_83, x_97);
x_99 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1(x_1, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_82, x_100);
lean_dec(x_82);
x_102 = lean_box_uint64(x_2);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_98);
x_104 = lean_array_uset(x_83, x_97, x_103);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_nat_mul(x_101, x_105);
x_107 = lean_unsigned_to_nat(3u);
x_108 = lean_nat_div(x_106, x_107);
lean_dec(x_106);
x_109 = lean_array_get_size(x_104);
x_110 = lean_nat_dec_le(x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__2(x_104);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_11, 0, x_112);
x_113 = lean_st_ref_set(x_4, x_11, x_12);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_box(0);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_101);
lean_ctor_set(x_118, 1, x_104);
lean_ctor_set(x_11, 0, x_118);
x_119 = lean_st_ref_set(x_4, x_11, x_12);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_124 = lean_box(0);
x_125 = lean_array_uset(x_83, x_97, x_124);
x_126 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(x_1, x_2, x_98);
x_127 = lean_array_uset(x_125, x_97, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_82);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_11, 0, x_128);
x_129 = lean_st_ref_set(x_4, x_11, x_12);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_11, 0);
x_135 = lean_ctor_get(x_11, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_11);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
x_137 = lean_array_get_size(x_136);
lean_dec(x_136);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_lt(x_138, x_137);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_1);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_134);
lean_ctor_set(x_140, 1, x_135);
x_141 = lean_st_ref_set(x_4, x_140, x_12);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; size_t x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; size_t x_158; size_t x_159; size_t x_160; size_t x_161; size_t x_162; lean_object* x_163; uint8_t x_164; 
x_146 = lean_ctor_get(x_134, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_134, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_148 = x_134;
} else {
 lean_dec_ref(x_134);
 x_148 = lean_box(0);
}
x_149 = lean_array_get_size(x_147);
x_150 = lean_ptr_addr(x_1);
x_151 = lean_usize_to_uint64(x_150);
x_152 = 32;
x_153 = lean_uint64_shift_right(x_151, x_152);
x_154 = lean_uint64_xor(x_151, x_153);
x_155 = 16;
x_156 = lean_uint64_shift_right(x_154, x_155);
x_157 = lean_uint64_xor(x_154, x_156);
x_158 = lean_uint64_to_usize(x_157);
x_159 = lean_usize_of_nat(x_149);
lean_dec(x_149);
x_160 = 1;
x_161 = lean_usize_sub(x_159, x_160);
x_162 = lean_usize_land(x_158, x_161);
x_163 = lean_array_uget(x_147, x_162);
x_164 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1(x_1, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_add(x_146, x_165);
lean_dec(x_146);
x_167 = lean_box_uint64(x_2);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_163);
x_169 = lean_array_uset(x_147, x_162, x_168);
x_170 = lean_unsigned_to_nat(4u);
x_171 = lean_nat_mul(x_166, x_170);
x_172 = lean_unsigned_to_nat(3u);
x_173 = lean_nat_div(x_171, x_172);
lean_dec(x_171);
x_174 = lean_array_get_size(x_169);
x_175 = lean_nat_dec_le(x_173, x_174);
lean_dec(x_174);
lean_dec(x_173);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__2(x_169);
if (lean_is_scalar(x_148)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_148;
}
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_135);
x_179 = lean_st_ref_set(x_4, x_178, x_12);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
if (lean_is_scalar(x_148)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_148;
}
lean_ctor_set(x_184, 0, x_166);
lean_ctor_set(x_184, 1, x_169);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_135);
x_186 = lean_st_ref_set(x_4, x_185, x_12);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_191 = lean_box(0);
x_192 = lean_array_uset(x_147, x_162, x_191);
x_193 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(x_1, x_2, x_163);
x_194 = lean_array_uset(x_192, x_162, x_193);
if (lean_is_scalar(x_148)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_148;
}
lean_ctor_set(x_195, 0, x_146);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_135);
x_197 = lean_st_ref_set(x_4, x_196, x_12);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___spec__6(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_st_ref_get(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVarsCore(x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_5, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_17);
x_23 = lean_st_ref_set(x_5, x_19, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_19, 3);
x_31 = lean_ctor_get(x_19, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_st_ref_set(x_5, x_32, x_20);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint64_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_5, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_nat_sub(x_3, x_5);
x_25 = lean_nat_sub(x_24, x_19);
lean_dec(x_24);
x_26 = l_Lean_Expr_getRevArg_x21(x_1, x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_31 = lean_uint64_mix_hash(x_8, x_30);
x_32 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_32;
x_8 = x_31;
x_15 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_array_fget(x_21, x_5);
x_39 = l_Lean_Meta_ParamInfo_isExplicit(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
x_40 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_40;
goto _start;
}
else
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_38, sizeof(void*)*1 + 2);
lean_dec(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_nat_sub(x_3, x_5);
x_44 = lean_nat_sub(x_43, x_19);
lean_dec(x_43);
x_45 = l_Lean_Expr_getRevArg_x21(x_1, x_44);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_46 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_45, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_50 = lean_uint64_mix_hash(x_8, x_49);
x_51 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_51;
x_8 = x_50;
x_15 = x_48;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
x_57 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_57;
goto _start;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_59 = lean_box_uint64(x_8);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_15);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_61 = lean_box_uint64(x_8);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_15);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(lean_object* x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box_uint64(x_2);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box_uint64(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_getFunInfo(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_unbox_uint64(x_15);
lean_dec(x_15);
lean_inc(x_18);
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__2(x_2, x_12, x_18, x_18, x_17, x_18, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_18);
lean_dec(x_12);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_14; uint8_t x_15; 
lean_free_object(x_9);
lean_inc(x_1);
x_14 = l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_expr_eqv(x_16, x_1);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unbox_uint64(x_20);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint64_t x_28; lean_object* x_29; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_29 = lean_box_uint64(x_28);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_expr_eqv(x_30, x_1);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox_uint64(x_34);
lean_dec(x_34);
x_37 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint64_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_43 = lean_box_uint64(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
}
case 4:
{
lean_object* x_45; uint64_t x_46; lean_object* x_47; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Name_hash___override(x_45);
lean_dec(x_45);
x_47 = lean_box_uint64(x_46);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
case 5:
{
lean_object* x_48; uint8_t x_49; 
lean_free_object(x_9);
x_48 = l_Lean_Expr_getAppFn(x_1);
x_49 = l_Lean_Expr_isMVar(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(x_48, x_1, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_1);
x_52 = l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_expr_eqv(x_53, x_1);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_48);
lean_dec(x_1);
x_56 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_65 = lean_box(0);
x_66 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(x_48, x_1, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_54);
lean_dec(x_1);
return x_66;
}
}
}
case 6:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_9);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_71);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_unbox_uint64(x_70);
lean_dec(x_70);
x_76 = lean_unbox_uint64(x_74);
lean_dec(x_74);
x_77 = lean_uint64_mix_hash(x_75, x_76);
x_78 = lean_box_uint64(x_77);
lean_ctor_set(x_72, 0, x_78);
return x_72;
}
else
{
lean_object* x_79; lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_72);
x_81 = lean_unbox_uint64(x_70);
lean_dec(x_70);
x_82 = lean_unbox_uint64(x_79);
lean_dec(x_79);
x_83 = lean_uint64_mix_hash(x_81, x_82);
x_84 = lean_box_uint64(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_70);
x_86 = !lean_is_exclusive(x_72);
if (x_86 == 0)
{
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_72, 0);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_72);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_90 = !lean_is_exclusive(x_69);
if (x_90 == 0)
{
return x_69;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_69, 0);
x_92 = lean_ctor_get(x_69, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_69);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
case 7:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_9);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 2);
lean_inc(x_95);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_96 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_unbox_uint64(x_97);
lean_dec(x_97);
x_103 = lean_unbox_uint64(x_101);
lean_dec(x_101);
x_104 = lean_uint64_mix_hash(x_102, x_103);
x_105 = lean_box_uint64(x_104);
lean_ctor_set(x_99, 0, x_105);
return x_99;
}
else
{
lean_object* x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_99, 0);
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_99);
x_108 = lean_unbox_uint64(x_97);
lean_dec(x_97);
x_109 = lean_unbox_uint64(x_106);
lean_dec(x_106);
x_110 = lean_uint64_mix_hash(x_108, x_109);
x_111 = lean_box_uint64(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_dec(x_97);
x_113 = !lean_is_exclusive(x_99);
if (x_113 == 0)
{
return x_99;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_99, 0);
x_115 = lean_ctor_get(x_99, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_99);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_95);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_96);
if (x_117 == 0)
{
return x_96;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_96, 0);
x_119 = lean_ctor_get(x_96, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_96);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
case 8:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_9);
x_121 = lean_ctor_get(x_1, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_1, 3);
lean_inc(x_122);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_123 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_125);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_unbox_uint64(x_124);
lean_dec(x_124);
x_130 = lean_unbox_uint64(x_128);
lean_dec(x_128);
x_131 = lean_uint64_mix_hash(x_129, x_130);
x_132 = lean_box_uint64(x_131);
lean_ctor_set(x_126, 0, x_132);
return x_126;
}
else
{
lean_object* x_133; lean_object* x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_ctor_get(x_126, 0);
x_134 = lean_ctor_get(x_126, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_126);
x_135 = lean_unbox_uint64(x_124);
lean_dec(x_124);
x_136 = lean_unbox_uint64(x_133);
lean_dec(x_133);
x_137 = lean_uint64_mix_hash(x_135, x_136);
x_138 = lean_box_uint64(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_124);
x_140 = !lean_is_exclusive(x_126);
if (x_140 == 0)
{
return x_126;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_126, 0);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_126);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_122);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_144 = !lean_is_exclusive(x_123);
if (x_144 == 0)
{
return x_123;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_123, 0);
x_146 = lean_ctor_get(x_123, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_123);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
case 10:
{
lean_object* x_148; lean_object* x_149; 
lean_free_object(x_9);
x_148 = lean_ctor_get(x_1, 1);
lean_inc(x_148);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_149 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint64_t x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unbox_uint64(x_150);
lean_dec(x_150);
x_153 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(x_1, x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_151);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_153;
}
else
{
uint8_t x_154; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_149);
if (x_154 == 0)
{
return x_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_149, 0);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_149);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
case 11:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_free_object(x_9);
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_1, 2);
lean_inc(x_159);
lean_dec(x_1);
x_160 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_uint64_of_nat(x_158);
lean_dec(x_158);
x_164 = lean_unbox_uint64(x_162);
lean_dec(x_162);
x_165 = lean_uint64_mix_hash(x_163, x_164);
x_166 = lean_box_uint64(x_165);
lean_ctor_set(x_160, 0, x_166);
return x_160;
}
else
{
lean_object* x_167; lean_object* x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_160, 0);
x_168 = lean_ctor_get(x_160, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_160);
x_169 = lean_uint64_of_nat(x_158);
lean_dec(x_158);
x_170 = lean_unbox_uint64(x_167);
lean_dec(x_167);
x_171 = lean_uint64_mix_hash(x_169, x_170);
x_172 = lean_box_uint64(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_168);
return x_173;
}
}
else
{
uint8_t x_174; 
lean_dec(x_158);
x_174 = !lean_is_exclusive(x_160);
if (x_174 == 0)
{
return x_160;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_160, 0);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_160);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
default: 
{
uint64_t x_178; lean_object* x_179; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_178 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_179 = lean_box_uint64(x_178);
lean_ctor_set(x_9, 0, x_179);
return x_9;
}
}
}
else
{
lean_object* x_180; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_180 = lean_ctor_get(x_13, 0);
lean_inc(x_180);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_180);
return x_9;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_9, 0);
x_182 = lean_ctor_get(x_9, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_9);
x_183 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_181);
lean_dec(x_181);
if (lean_obj_tag(x_183) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_inc(x_1);
x_184 = l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_expr_eqv(x_185, x_1);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_187);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_189 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; uint64_t x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_unbox_uint64(x_190);
lean_dec(x_190);
x_193 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(x_1, x_192, x_2, x_3, x_4, x_5, x_6, x_7, x_191);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_196 = x_189;
} else {
 lean_dec_ref(x_189);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
uint64_t x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_185);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_198 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_199 = lean_box_uint64(x_198);
if (lean_is_scalar(x_187)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_187;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_186);
return x_200;
}
}
case 4:
{
lean_object* x_201; uint64_t x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_201 = lean_ctor_get(x_1, 0);
lean_inc(x_201);
lean_dec(x_1);
x_202 = l_Lean_Name_hash___override(x_201);
lean_dec(x_201);
x_203 = lean_box_uint64(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_182);
return x_204;
}
case 5:
{
lean_object* x_205; uint8_t x_206; 
x_205 = l_Lean_Expr_getAppFn(x_1);
x_206 = l_Lean_Expr_isMVar(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_box(0);
x_208 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(x_205, x_1, x_207, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
lean_dec(x_1);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_inc(x_1);
x_209 = l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_expr_eqv(x_210, x_1);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_205);
lean_dec(x_1);
x_213 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_210, x_2, x_3, x_4, x_5, x_6, x_7, x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_220 = x_213;
} else {
 lean_dec_ref(x_213);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_210);
x_222 = lean_box(0);
x_223 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(x_205, x_1, x_222, x_2, x_3, x_4, x_5, x_6, x_7, x_211);
lean_dec(x_1);
return x_223;
}
}
}
case 6:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_1, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_1, 2);
lean_inc(x_225);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_226 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_224, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; lean_object* x_236; lean_object* x_237; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_232 = x_229;
} else {
 lean_dec_ref(x_229);
 x_232 = lean_box(0);
}
x_233 = lean_unbox_uint64(x_227);
lean_dec(x_227);
x_234 = lean_unbox_uint64(x_230);
lean_dec(x_230);
x_235 = lean_uint64_mix_hash(x_233, x_234);
x_236 = lean_box_uint64(x_235);
if (lean_is_scalar(x_232)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_232;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_231);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_227);
x_238 = lean_ctor_get(x_229, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_229, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_240 = x_229;
} else {
 lean_dec_ref(x_229);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_225);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_242 = lean_ctor_get(x_226, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_226, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_244 = x_226;
} else {
 lean_dec_ref(x_226);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
case 7:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_1, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_1, 2);
lean_inc(x_247);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_248 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_246, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_247, x_2, x_3, x_4, x_5, x_6, x_7, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; uint64_t x_255; uint64_t x_256; uint64_t x_257; lean_object* x_258; lean_object* x_259; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = lean_unbox_uint64(x_249);
lean_dec(x_249);
x_256 = lean_unbox_uint64(x_252);
lean_dec(x_252);
x_257 = lean_uint64_mix_hash(x_255, x_256);
x_258 = lean_box_uint64(x_257);
if (lean_is_scalar(x_254)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_254;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_253);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_249);
x_260 = lean_ctor_get(x_251, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_251, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_262 = x_251;
} else {
 lean_dec_ref(x_251);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_247);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_264 = lean_ctor_get(x_248, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_248, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_266 = x_248;
} else {
 lean_dec_ref(x_248);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
case 8:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_1, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_1, 3);
lean_inc(x_269);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_270 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_269, x_2, x_3, x_4, x_5, x_6, x_7, x_272);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint64_t x_277; uint64_t x_278; uint64_t x_279; lean_object* x_280; lean_object* x_281; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = lean_unbox_uint64(x_271);
lean_dec(x_271);
x_278 = lean_unbox_uint64(x_274);
lean_dec(x_274);
x_279 = lean_uint64_mix_hash(x_277, x_278);
x_280 = lean_box_uint64(x_279);
if (lean_is_scalar(x_276)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_276;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_275);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_271);
x_282 = lean_ctor_get(x_273, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_273, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_284 = x_273;
} else {
 lean_dec_ref(x_273);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_269);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_286 = lean_ctor_get(x_270, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_270, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_288 = x_270;
} else {
 lean_dec_ref(x_270);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
case 10:
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_1, 1);
lean_inc(x_290);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_291 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_290, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint64_t x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_unbox_uint64(x_292);
lean_dec(x_292);
x_295 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(x_1, x_294, x_2, x_3, x_4, x_5, x_6, x_7, x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_296 = lean_ctor_get(x_291, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_291, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_298 = x_291;
} else {
 lean_dec_ref(x_291);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
case 11:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_1, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_1, 2);
lean_inc(x_301);
lean_dec(x_1);
x_302 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_301, x_2, x_3, x_4, x_5, x_6, x_7, x_182);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint64_t x_306; uint64_t x_307; uint64_t x_308; lean_object* x_309; lean_object* x_310; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = lean_uint64_of_nat(x_300);
lean_dec(x_300);
x_307 = lean_unbox_uint64(x_303);
lean_dec(x_303);
x_308 = lean_uint64_mix_hash(x_306, x_307);
x_309 = lean_box_uint64(x_308);
if (lean_is_scalar(x_305)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_305;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_304);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_300);
x_311 = lean_ctor_get(x_302, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_302, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_313 = x_302;
} else {
 lean_dec_ref(x_302);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
default: 
{
uint64_t x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_315 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_316 = lean_box_uint64(x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_182);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_318 = lean_ctor_get(x_183, 0);
lean_inc(x_318);
lean_dec(x_183);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_182);
return x_319;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___lambda__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Canonicalizer_canon_unsafe__1___spec__1(uint64_t x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_1, x_6);
x_8 = lean_uint64_xor(x_1, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_4, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Canonicalizer_canon_unsafe__1___spec__1(x_1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Canonicalizer_canon_unsafe__1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Meta_Canonicalizer_canon_unsafe__1___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_Meta_Canonicalizer_canon_unsafe__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(uint64_t x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_7 = lean_uint64_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__4___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = lean_unbox_uint64(x_4);
x_9 = lean_uint64_shift_right(x_8, x_7);
x_10 = lean_unbox_uint64(x_4);
x_11 = lean_uint64_xor(x_10, x_9);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_1, x_19);
lean_ctor_set(x_2, 2, x_20);
x_21 = lean_array_uset(x_1, x_19, x_2);
x_1 = x_21;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_26 = lean_array_get_size(x_1);
x_27 = 32;
x_28 = lean_unbox_uint64(x_23);
x_29 = lean_uint64_shift_right(x_28, x_27);
x_30 = lean_unbox_uint64(x_23);
x_31 = lean_uint64_xor(x_30, x_29);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_1, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
x_42 = lean_array_uset(x_1, x_39, x_41);
x_1 = x_42;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__4___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_unbox_uint64(x_6);
x_10 = lean_uint64_dec_eq(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_11);
return x_3;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_box_uint64(x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = lean_unbox_uint64(x_13);
x_17 = lean_uint64_dec_eq(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_1, x_2, x_15);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_box_uint64(x_1);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_take(x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_13, 1);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 0, x_1);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_get_size(x_19);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_2, x_21);
x_23 = lean_uint64_xor(x_2, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_19, x_31);
lean_inc(x_32);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_18, x_34);
lean_dec(x_18);
x_36 = lean_box_uint64(x_2);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
lean_ctor_set(x_37, 2, x_32);
x_38 = lean_array_uset(x_19, x_31, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_35, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_38);
lean_ctor_set(x_16, 1, x_45);
lean_ctor_set(x_16, 0, x_35);
x_46 = lean_st_ref_set(x_5, x_13, x_15);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_ctor_set(x_16, 1, x_38);
lean_ctor_set(x_16, 0, x_35);
x_53 = lean_st_ref_set(x_5, x_13, x_15);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_19, x_31, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_11, x_32);
x_63 = lean_array_uset(x_61, x_31, x_62);
lean_ctor_set(x_16, 1, x_63);
x_64 = lean_st_ref_set(x_5, x_13, x_15);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_71 = lean_ctor_get(x_16, 0);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_16);
x_73 = lean_array_get_size(x_72);
x_74 = 32;
x_75 = lean_uint64_shift_right(x_2, x_74);
x_76 = lean_uint64_xor(x_2, x_75);
x_77 = 16;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_82 = 1;
x_83 = lean_usize_sub(x_81, x_82);
x_84 = lean_usize_land(x_80, x_83);
x_85 = lean_array_uget(x_72, x_84);
lean_inc(x_85);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_71, x_87);
lean_dec(x_71);
x_89 = lean_box_uint64(x_2);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_11);
lean_ctor_set(x_90, 2, x_85);
x_91 = lean_array_uset(x_72, x_84, x_90);
x_92 = lean_unsigned_to_nat(4u);
x_93 = lean_nat_mul(x_88, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_13, 1, x_99);
x_100 = lean_st_ref_set(x_5, x_13, x_15);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_88);
lean_ctor_set(x_105, 1, x_91);
lean_ctor_set(x_13, 1, x_105);
x_106 = lean_st_ref_set(x_5, x_13, x_15);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_72, x_84, x_111);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_11, x_85);
x_114 = lean_array_uset(x_112, x_84, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_71);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_13, 1, x_115);
x_116 = lean_st_ref_set(x_5, x_13, x_15);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; size_t x_134; size_t x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint8_t x_140; 
x_121 = lean_ctor_get(x_11, 1);
x_122 = lean_ctor_get(x_13, 0);
x_123 = lean_ctor_get(x_13, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 0, x_1);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_array_get_size(x_125);
x_128 = 32;
x_129 = lean_uint64_shift_right(x_2, x_128);
x_130 = lean_uint64_xor(x_2, x_129);
x_131 = 16;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = lean_uint64_to_usize(x_133);
x_135 = lean_usize_of_nat(x_127);
lean_dec(x_127);
x_136 = 1;
x_137 = lean_usize_sub(x_135, x_136);
x_138 = lean_usize_land(x_134, x_137);
x_139 = lean_array_uget(x_125, x_138);
lean_inc(x_139);
x_140 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_add(x_124, x_141);
lean_dec(x_124);
x_143 = lean_box_uint64(x_2);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_11);
lean_ctor_set(x_144, 2, x_139);
x_145 = lean_array_uset(x_125, x_138, x_144);
x_146 = lean_unsigned_to_nat(4u);
x_147 = lean_nat_mul(x_142, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_145);
if (lean_is_scalar(x_126)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_126;
}
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_122);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_st_ref_set(x_5, x_154, x_121);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
if (lean_is_scalar(x_126)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_126;
}
lean_ctor_set(x_160, 0, x_142);
lean_ctor_set(x_160, 1, x_145);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_122);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_st_ref_set(x_5, x_161, x_121);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_167 = lean_box(0);
x_168 = lean_array_uset(x_125, x_138, x_167);
x_169 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_11, x_139);
x_170 = lean_array_uset(x_168, x_138, x_169);
if (lean_is_scalar(x_126)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_126;
}
lean_ctor_set(x_171, 0, x_124);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_122);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_st_ref_set(x_5, x_172, x_121);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint64_t x_188; uint64_t x_189; uint64_t x_190; uint64_t x_191; uint64_t x_192; uint64_t x_193; size_t x_194; size_t x_195; size_t x_196; size_t x_197; size_t x_198; lean_object* x_199; uint8_t x_200; 
x_178 = lean_ctor_get(x_11, 0);
x_179 = lean_ctor_get(x_11, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_11);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_182 = x_178;
} else {
 lean_dec_ref(x_178);
 x_182 = lean_box(0);
}
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_3);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_186 = x_181;
} else {
 lean_dec_ref(x_181);
 x_186 = lean_box(0);
}
x_187 = lean_array_get_size(x_185);
x_188 = 32;
x_189 = lean_uint64_shift_right(x_2, x_188);
x_190 = lean_uint64_xor(x_2, x_189);
x_191 = 16;
x_192 = lean_uint64_shift_right(x_190, x_191);
x_193 = lean_uint64_xor(x_190, x_192);
x_194 = lean_uint64_to_usize(x_193);
x_195 = lean_usize_of_nat(x_187);
lean_dec(x_187);
x_196 = 1;
x_197 = lean_usize_sub(x_195, x_196);
x_198 = lean_usize_land(x_194, x_197);
x_199 = lean_array_uget(x_185, x_198);
lean_inc(x_199);
x_200 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_201 = lean_unsigned_to_nat(1u);
x_202 = lean_nat_add(x_184, x_201);
lean_dec(x_184);
x_203 = lean_box_uint64(x_2);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_183);
lean_ctor_set(x_204, 2, x_199);
x_205 = lean_array_uset(x_185, x_198, x_204);
x_206 = lean_unsigned_to_nat(4u);
x_207 = lean_nat_mul(x_202, x_206);
x_208 = lean_unsigned_to_nat(3u);
x_209 = lean_nat_div(x_207, x_208);
lean_dec(x_207);
x_210 = lean_array_get_size(x_205);
x_211 = lean_nat_dec_le(x_209, x_210);
lean_dec(x_210);
lean_dec(x_209);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_212 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_205);
if (lean_is_scalar(x_186)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_186;
}
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_182)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_182;
}
lean_ctor_set(x_214, 0, x_180);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_st_ref_set(x_5, x_214, x_179);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_box(0);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_scalar(x_186)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_186;
}
lean_ctor_set(x_220, 0, x_202);
lean_ctor_set(x_220, 1, x_205);
if (lean_is_scalar(x_182)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_182;
}
lean_ctor_set(x_221, 0, x_180);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_st_ref_set(x_5, x_221, x_179);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = lean_box(0);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_227 = lean_box(0);
x_228 = lean_array_uset(x_185, x_198, x_227);
x_229 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_183, x_199);
x_230 = lean_array_uset(x_228, x_198, x_229);
if (lean_is_scalar(x_186)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_186;
}
lean_ctor_set(x_231, 0, x_184);
lean_ctor_set(x_231, 1, x_230);
if (lean_is_scalar(x_182)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_182;
}
lean_ctor_set(x_232, 0, x_180);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_st_ref_set(x_5, x_232, x_179);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
x_236 = lean_box(0);
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_235;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_234);
return x_237;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint64_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_Canonicalizer_canon_unsafe__2(x_1, x_11, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__3(lean_object* x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_1);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_array_get_size(x_19);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_2, x_21);
x_23 = lean_uint64_xor(x_2, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_19, x_31);
lean_inc(x_32);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_18, x_34);
lean_dec(x_18);
x_36 = lean_box_uint64(x_2);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_10);
lean_ctor_set(x_37, 2, x_32);
x_38 = lean_array_uset(x_19, x_31, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_35, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_38);
lean_ctor_set(x_15, 1, x_45);
lean_ctor_set(x_15, 0, x_35);
x_46 = lean_st_ref_set(x_4, x_12, x_14);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_ctor_set(x_15, 1, x_38);
lean_ctor_set(x_15, 0, x_35);
x_53 = lean_st_ref_set(x_4, x_12, x_14);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_19, x_31, x_60);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_10, x_32);
x_63 = lean_array_uset(x_61, x_31, x_62);
lean_ctor_set(x_15, 1, x_63);
x_64 = lean_st_ref_set(x_4, x_12, x_14);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_array_get_size(x_72);
x_74 = 32;
x_75 = lean_uint64_shift_right(x_2, x_74);
x_76 = lean_uint64_xor(x_2, x_75);
x_77 = 16;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_82 = 1;
x_83 = lean_usize_sub(x_81, x_82);
x_84 = lean_usize_land(x_80, x_83);
x_85 = lean_array_uget(x_72, x_84);
lean_inc(x_85);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_71, x_87);
lean_dec(x_71);
x_89 = lean_box_uint64(x_2);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_10);
lean_ctor_set(x_90, 2, x_85);
x_91 = lean_array_uset(x_72, x_84, x_90);
x_92 = lean_unsigned_to_nat(4u);
x_93 = lean_nat_mul(x_88, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_12, 1, x_99);
x_100 = lean_st_ref_set(x_4, x_12, x_14);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_88);
lean_ctor_set(x_105, 1, x_91);
lean_ctor_set(x_12, 1, x_105);
x_106 = lean_st_ref_set(x_4, x_12, x_14);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_box(0);
x_112 = lean_array_uset(x_72, x_84, x_111);
x_113 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_10, x_85);
x_114 = lean_array_uset(x_112, x_84, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_71);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_12, 1, x_115);
x_116 = lean_st_ref_set(x_4, x_12, x_14);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; size_t x_135; size_t x_136; size_t x_137; size_t x_138; size_t x_139; lean_object* x_140; uint8_t x_141; 
x_121 = lean_ctor_get(x_10, 1);
x_122 = lean_ctor_get(x_12, 0);
x_123 = lean_ctor_get(x_12, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_12);
x_124 = lean_box(0);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_124);
lean_ctor_set(x_10, 0, x_1);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = lean_array_get_size(x_126);
x_129 = 32;
x_130 = lean_uint64_shift_right(x_2, x_129);
x_131 = lean_uint64_xor(x_2, x_130);
x_132 = 16;
x_133 = lean_uint64_shift_right(x_131, x_132);
x_134 = lean_uint64_xor(x_131, x_133);
x_135 = lean_uint64_to_usize(x_134);
x_136 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_137 = 1;
x_138 = lean_usize_sub(x_136, x_137);
x_139 = lean_usize_land(x_135, x_138);
x_140 = lean_array_uget(x_126, x_139);
lean_inc(x_140);
x_141 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_125, x_142);
lean_dec(x_125);
x_144 = lean_box_uint64(x_2);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_10);
lean_ctor_set(x_145, 2, x_140);
x_146 = lean_array_uset(x_126, x_139, x_145);
x_147 = lean_unsigned_to_nat(4u);
x_148 = lean_nat_mul(x_143, x_147);
x_149 = lean_unsigned_to_nat(3u);
x_150 = lean_nat_div(x_148, x_149);
lean_dec(x_148);
x_151 = lean_array_get_size(x_146);
x_152 = lean_nat_dec_le(x_150, x_151);
lean_dec(x_151);
lean_dec(x_150);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_146);
if (lean_is_scalar(x_127)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_127;
}
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_122);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_st_ref_set(x_4, x_155, x_121);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
if (lean_is_scalar(x_127)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_127;
}
lean_ctor_set(x_161, 0, x_143);
lean_ctor_set(x_161, 1, x_146);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_122);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_st_ref_set(x_4, x_162, x_121);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_box(0);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_168 = lean_box(0);
x_169 = lean_array_uset(x_126, x_139, x_168);
x_170 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_10, x_140);
x_171 = lean_array_uset(x_169, x_139, x_170);
if (lean_is_scalar(x_127)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_127;
}
lean_ctor_set(x_172, 0, x_125);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_122);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_st_ref_set(x_4, x_173, x_121);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
x_177 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_176;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint64_t x_190; uint64_t x_191; uint64_t x_192; uint64_t x_193; uint64_t x_194; uint64_t x_195; size_t x_196; size_t x_197; size_t x_198; size_t x_199; size_t x_200; lean_object* x_201; uint8_t x_202; 
x_179 = lean_ctor_get(x_10, 0);
x_180 = lean_ctor_get(x_10, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_10);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_1);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_188 = x_182;
} else {
 lean_dec_ref(x_182);
 x_188 = lean_box(0);
}
x_189 = lean_array_get_size(x_187);
x_190 = 32;
x_191 = lean_uint64_shift_right(x_2, x_190);
x_192 = lean_uint64_xor(x_2, x_191);
x_193 = 16;
x_194 = lean_uint64_shift_right(x_192, x_193);
x_195 = lean_uint64_xor(x_192, x_194);
x_196 = lean_uint64_to_usize(x_195);
x_197 = lean_usize_of_nat(x_189);
lean_dec(x_189);
x_198 = 1;
x_199 = lean_usize_sub(x_197, x_198);
x_200 = lean_usize_land(x_196, x_199);
x_201 = lean_array_uget(x_187, x_200);
lean_inc(x_201);
x_202 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__1(x_2, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_nat_add(x_186, x_203);
lean_dec(x_186);
x_205 = lean_box_uint64(x_2);
x_206 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_185);
lean_ctor_set(x_206, 2, x_201);
x_207 = lean_array_uset(x_187, x_200, x_206);
x_208 = lean_unsigned_to_nat(4u);
x_209 = lean_nat_mul(x_204, x_208);
x_210 = lean_unsigned_to_nat(3u);
x_211 = lean_nat_div(x_209, x_210);
lean_dec(x_209);
x_212 = lean_array_get_size(x_207);
x_213 = lean_nat_dec_le(x_211, x_212);
lean_dec(x_212);
lean_dec(x_211);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_214 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__2(x_207);
if (lean_is_scalar(x_188)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_188;
}
lean_ctor_set(x_215, 0, x_204);
lean_ctor_set(x_215, 1, x_214);
if (lean_is_scalar(x_183)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_183;
}
lean_ctor_set(x_216, 0, x_181);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_st_ref_set(x_4, x_216, x_180);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = lean_box(0);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
if (lean_is_scalar(x_188)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_188;
}
lean_ctor_set(x_222, 0, x_204);
lean_ctor_set(x_222, 1, x_207);
if (lean_is_scalar(x_183)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_183;
}
lean_ctor_set(x_223, 0, x_181);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_st_ref_set(x_4, x_223, x_180);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_229 = lean_box(0);
x_230 = lean_array_uset(x_187, x_200, x_229);
x_231 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Canonicalizer_canon_unsafe__2___spec__6(x_2, x_185, x_201);
x_232 = lean_array_uset(x_230, x_200, x_231);
if (lean_is_scalar(x_188)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_188;
}
lean_ctor_set(x_233, 0, x_186);
lean_ctor_set(x_233, 1, x_232);
if (lean_is_scalar(x_183)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_183;
}
lean_ctor_set(x_234, 0, x_181);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_st_ref_set(x_4, x_234, x_180);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
x_238 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_237;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_Canonicalizer_canon_unsafe__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
lean_inc(x_1);
x_16 = l_Lean_Meta_isExprDefEq(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_3);
lean_dec(x_14);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_19;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_14);
x_24 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_24);
lean_ctor_set(x_3, 0, x_23);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_14);
x_27 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_free_object(x_3);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_33);
lean_inc(x_1);
x_35 = l_Lean_Meta_isExprDefEq(x_1, x_33, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_34;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_38;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_33);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___lambda__1(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_12 = l_Lean_Meta_Canonicalizer_canon_unsafe__2(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_canon___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unbox_uint64(x_10);
x_16 = l_Lean_Meta_Canonicalizer_canon_unsafe__1(x_15, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
uint64_t x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unbox_uint64(x_10);
lean_dec(x_10);
lean_inc(x_1);
x_18 = l_Lean_Meta_Canonicalizer_canon_unsafe__3(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_4, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_ctor_set_uint8(x_23, 9, x_2);
x_28 = l_Lean_Meta_Canonicalizer_canon___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
lean_inc(x_1);
x_29 = l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1(x_1, x_28, x_24, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_35 = l_Lean_Meta_Canonicalizer_canon___lambda__1(x_1, x_34, x_24, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_4);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_29, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_42);
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_4);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get_uint8(x_23, 0);
x_51 = lean_ctor_get_uint8(x_23, 1);
x_52 = lean_ctor_get_uint8(x_23, 2);
x_53 = lean_ctor_get_uint8(x_23, 3);
x_54 = lean_ctor_get_uint8(x_23, 4);
x_55 = lean_ctor_get_uint8(x_23, 5);
x_56 = lean_ctor_get_uint8(x_23, 6);
x_57 = lean_ctor_get_uint8(x_23, 7);
x_58 = lean_ctor_get_uint8(x_23, 8);
x_59 = lean_ctor_get_uint8(x_23, 10);
x_60 = lean_ctor_get_uint8(x_23, 11);
x_61 = lean_ctor_get_uint8(x_23, 12);
lean_dec(x_23);
x_62 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_62, 0, x_50);
lean_ctor_set_uint8(x_62, 1, x_51);
lean_ctor_set_uint8(x_62, 2, x_52);
lean_ctor_set_uint8(x_62, 3, x_53);
lean_ctor_set_uint8(x_62, 4, x_54);
lean_ctor_set_uint8(x_62, 5, x_55);
lean_ctor_set_uint8(x_62, 6, x_56);
lean_ctor_set_uint8(x_62, 7, x_57);
lean_ctor_set_uint8(x_62, 8, x_58);
lean_ctor_set_uint8(x_62, 9, x_2);
lean_ctor_set_uint8(x_62, 10, x_59);
lean_ctor_set_uint8(x_62, 11, x_60);
lean_ctor_set_uint8(x_62, 12, x_61);
lean_ctor_set(x_4, 0, x_62);
x_63 = l_Lean_Meta_Canonicalizer_canon___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
lean_inc(x_1);
x_64 = l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1(x_1, x_63, x_24, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_70 = l_Lean_Meta_Canonicalizer_canon___lambda__1(x_1, x_69, x_24, x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_4);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
lean_dec(x_66);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_4);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_83 = lean_ctor_get(x_4, 1);
x_84 = lean_ctor_get(x_4, 2);
x_85 = lean_ctor_get(x_4, 3);
x_86 = lean_ctor_get(x_4, 4);
x_87 = lean_ctor_get(x_4, 5);
x_88 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_89 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_4);
x_90 = lean_ctor_get_uint8(x_23, 0);
x_91 = lean_ctor_get_uint8(x_23, 1);
x_92 = lean_ctor_get_uint8(x_23, 2);
x_93 = lean_ctor_get_uint8(x_23, 3);
x_94 = lean_ctor_get_uint8(x_23, 4);
x_95 = lean_ctor_get_uint8(x_23, 5);
x_96 = lean_ctor_get_uint8(x_23, 6);
x_97 = lean_ctor_get_uint8(x_23, 7);
x_98 = lean_ctor_get_uint8(x_23, 8);
x_99 = lean_ctor_get_uint8(x_23, 10);
x_100 = lean_ctor_get_uint8(x_23, 11);
x_101 = lean_ctor_get_uint8(x_23, 12);
if (lean_is_exclusive(x_23)) {
 x_102 = x_23;
} else {
 lean_dec_ref(x_23);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 0, 13);
} else {
 x_103 = x_102;
}
lean_ctor_set_uint8(x_103, 0, x_90);
lean_ctor_set_uint8(x_103, 1, x_91);
lean_ctor_set_uint8(x_103, 2, x_92);
lean_ctor_set_uint8(x_103, 3, x_93);
lean_ctor_set_uint8(x_103, 4, x_94);
lean_ctor_set_uint8(x_103, 5, x_95);
lean_ctor_set_uint8(x_103, 6, x_96);
lean_ctor_set_uint8(x_103, 7, x_97);
lean_ctor_set_uint8(x_103, 8, x_98);
lean_ctor_set_uint8(x_103, 9, x_2);
lean_ctor_set_uint8(x_103, 10, x_99);
lean_ctor_set_uint8(x_103, 11, x_100);
lean_ctor_set_uint8(x_103, 12, x_101);
x_104 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_83);
lean_ctor_set(x_104, 2, x_84);
lean_ctor_set(x_104, 3, x_85);
lean_ctor_set(x_104, 4, x_86);
lean_ctor_set(x_104, 5, x_87);
lean_ctor_set_uint8(x_104, sizeof(void*)*6, x_88);
lean_ctor_set_uint8(x_104, sizeof(void*)*6 + 1, x_89);
x_105 = l_Lean_Meta_Canonicalizer_canon___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_104);
lean_inc(x_24);
lean_inc(x_1);
x_106 = l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1(x_1, x_105, x_24, x_105, x_2, x_3, x_104, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_box(0);
x_111 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_112 = l_Lean_Meta_Canonicalizer_canon___lambda__1(x_1, x_111, x_24, x_110, x_2, x_3, x_104, x_5, x_6, x_7, x_109);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_104);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_104);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_117 = lean_ctor_get(x_106, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_118 = x_106;
} else {
 lean_dec_ref(x_106);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_108, 0);
lean_inc(x_119);
lean_dec(x_108);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_121 = lean_ctor_get(x_106, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_123 = x_106;
} else {
 lean_dec_ref(x_106);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_9);
if (x_125 == 0)
{
return x_9;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_9, 0);
x_127 = lean_ctor_get(x_9, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_9);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_List_forIn_loop___at_Lean_Meta_Canonicalizer_canon___spec__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Canonicalizer_canon___lambda__1(x_1, x_12, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_canon(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
lean_object* initialize_Lean_Data_HashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_FunInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1 = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4);
l_Lean_Meta_Canonicalizer_instInhabitedState = _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
l_Lean_Meta_Canonicalizer_canon___closed__1 = _init_l_Lean_Meta_Canonicalizer_canon___closed__1();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_canon___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
