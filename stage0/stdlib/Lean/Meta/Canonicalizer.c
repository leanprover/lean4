// Lean compiler output
// Module: Lean.Meta.Canonicalizer
// Imports: Lean.Util.ShareCommon Lean.Meta.Basic Lean.Meta.FunInfo Std.Data.HashMap.Raw
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
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object*, uint64_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4(lean_object*, uint64_t, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object*, uint64_t, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1(uint64_t, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__6;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited;
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_canon___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0(lean_object*, uint64_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Canonicalizer_instInhabitedState___closed__5;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_canon(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instBEqExprVisited() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Canonicalizer_instBEqExprVisited___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instHashableExprVisited() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Canonicalizer_instHashableExprVisited___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__6;
x_2 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Canonicalizer_instInhabitedState___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_dec(x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Canonicalizer_CanonM_run_x27(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Canonicalizer_CanonM_run___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Canonicalizer_CanonM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Canonicalizer_CanonM_run(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
size_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ptr_addr(x_1);
x_10 = lean_usize_to_uint64(x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_4, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(x_1, x_22);
lean_dec(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ptr_addr(x_5);
x_9 = lean_ptr_addr(x_1);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_11);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_ptr_addr(x_1);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(x_1, x_2, x_14);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_box(0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_20);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_free_object(x_16);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_1);
x_8 = x_21;
x_9 = x_6;
goto block_15;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_26 = lean_ctor_get(x_6, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_6, 0);
lean_dec(x_27);
x_28 = lean_ptr_addr(x_1);
x_29 = lean_usize_to_uint64(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(x_1, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_19, x_43);
lean_dec(x_19);
x_45 = lean_box_uint64(x_2);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_41);
x_47 = lean_array_uset(x_20, x_40, x_46);
x_48 = lean_unsigned_to_nat(4u);
x_49 = lean_nat_mul(x_44, x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_div(x_49, x_50);
lean_dec(x_49);
x_52 = lean_array_get_size(x_47);
x_53 = lean_nat_dec_le(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1___redArg(x_47);
lean_ctor_set(x_16, 1, x_54);
lean_ctor_set(x_16, 0, x_44);
x_8 = x_21;
x_9 = x_6;
goto block_15;
}
else
{
lean_ctor_set(x_16, 1, x_47);
lean_ctor_set(x_16, 0, x_44);
x_8 = x_21;
x_9 = x_6;
goto block_15;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_box(0);
x_56 = lean_array_uset(x_20, x_40, x_55);
x_57 = lean_box_uint64(x_2);
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(x_1, x_57, x_41);
x_59 = lean_array_uset(x_56, x_40, x_58);
lean_ctor_set(x_16, 1, x_59);
x_8 = x_21;
x_9 = x_6;
goto block_15;
}
}
else
{
size_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; size_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_6);
x_60 = lean_ptr_addr(x_1);
x_61 = lean_usize_to_uint64(x_60);
x_62 = 32;
x_63 = lean_uint64_shift_right(x_61, x_62);
x_64 = lean_uint64_xor(x_61, x_63);
x_65 = 16;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = lean_uint64_to_usize(x_67);
x_69 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_70 = 1;
x_71 = lean_usize_sub(x_69, x_70);
x_72 = lean_usize_land(x_68, x_71);
x_73 = lean_array_uget(x_20, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(x_1, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_19, x_75);
lean_dec(x_19);
x_77 = lean_box_uint64(x_2);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_73);
x_79 = lean_array_uset(x_20, x_72, x_78);
x_80 = lean_unsigned_to_nat(4u);
x_81 = lean_nat_mul(x_76, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = lean_nat_div(x_81, x_82);
lean_dec(x_81);
x_84 = lean_array_get_size(x_79);
x_85 = lean_nat_dec_le(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1___redArg(x_79);
lean_ctor_set(x_16, 1, x_86);
lean_ctor_set(x_16, 0, x_76);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_16);
lean_ctor_set(x_87, 1, x_17);
x_8 = x_21;
x_9 = x_87;
goto block_15;
}
else
{
lean_object* x_88; 
lean_ctor_set(x_16, 1, x_79);
lean_ctor_set(x_16, 0, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_16);
lean_ctor_set(x_88, 1, x_17);
x_8 = x_21;
x_9 = x_88;
goto block_15;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_box(0);
x_90 = lean_array_uset(x_20, x_72, x_89);
x_91 = lean_box_uint64(x_2);
x_92 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(x_1, x_91, x_73);
x_93 = lean_array_uset(x_90, x_72, x_92);
lean_ctor_set(x_16, 1, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_16);
lean_ctor_set(x_94, 1, x_17);
x_8 = x_21;
x_9 = x_94;
goto block_15;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_95 = lean_ctor_get(x_16, 0);
x_96 = lean_ctor_get(x_16, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_16);
x_97 = lean_box(0);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_array_get_size(x_96);
x_100 = lean_nat_dec_lt(x_98, x_99);
if (x_100 == 0)
{
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_17);
lean_dec(x_1);
x_8 = x_97;
x_9 = x_6;
goto block_15;
}
else
{
lean_object* x_101; size_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; size_t x_110; size_t x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_101 = x_6;
} else {
 lean_dec_ref(x_6);
 x_101 = lean_box(0);
}
x_102 = lean_ptr_addr(x_1);
x_103 = lean_usize_to_uint64(x_102);
x_104 = 32;
x_105 = lean_uint64_shift_right(x_103, x_104);
x_106 = lean_uint64_xor(x_103, x_105);
x_107 = 16;
x_108 = lean_uint64_shift_right(x_106, x_107);
x_109 = lean_uint64_xor(x_106, x_108);
x_110 = lean_uint64_to_usize(x_109);
x_111 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_112 = 1;
x_113 = lean_usize_sub(x_111, x_112);
x_114 = lean_usize_land(x_110, x_113);
x_115 = lean_array_uget(x_96, x_114);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(x_1, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_95, x_117);
lean_dec(x_95);
x_119 = lean_box_uint64(x_2);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_115);
x_121 = lean_array_uset(x_96, x_114, x_120);
x_122 = lean_unsigned_to_nat(4u);
x_123 = lean_nat_mul(x_118, x_122);
x_124 = lean_unsigned_to_nat(3u);
x_125 = lean_nat_div(x_123, x_124);
lean_dec(x_123);
x_126 = lean_array_get_size(x_121);
x_127 = lean_nat_dec_le(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__1___redArg(x_121);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_128);
if (lean_is_scalar(x_101)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_101;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_17);
x_8 = x_97;
x_9 = x_130;
goto block_15;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_118);
lean_ctor_set(x_131, 1, x_121);
if (lean_is_scalar(x_101)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_101;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_17);
x_8 = x_97;
x_9 = x_132;
goto block_15;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_box(0);
x_134 = lean_array_uset(x_96, x_114, x_133);
x_135 = lean_box_uint64(x_2);
x_136 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__4___redArg(x_1, x_135, x_115);
x_137 = lean_array_uset(x_134, x_114, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_95);
lean_ctor_set(x_138, 1, x_137);
if (lean_is_scalar(x_101)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_101;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_17);
x_8 = x_97;
x_9 = x_139;
goto block_15;
}
}
}
block_15:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_set(x_3, x_9, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(lean_object* x_1, uint64_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(x_1, x_2, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint8_t x_21; uint8_t x_32; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_32 = lean_nat_dec_lt(x_6, x_14);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_33 = lean_box_uint64(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_13);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_array_get_size(x_35);
x_37 = lean_nat_dec_lt(x_6, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_nat_sub(x_1, x_6);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_Expr_getRevArg_x21(x_2, x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_42 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint64_t x_45; uint64_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unbox_uint64(x_43);
lean_dec(x_43);
x_46 = lean_uint64_mix_hash(x_5, x_45);
x_16 = x_46;
x_17 = x_44;
goto block_20;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
return x_42;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_array_fget(x_35, x_6);
x_48 = l_Lean_Meta_ParamInfo_isExplicit(x_47);
if (x_48 == 0)
{
lean_dec(x_47);
x_21 = x_48;
goto block_31;
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_47, sizeof(void*)*1 + 2);
lean_dec(x_47);
if (x_49 == 0)
{
x_21 = x_48;
goto block_31;
}
else
{
x_16 = x_5;
x_17 = x_13;
goto block_20;
}
}
}
}
block_20:
{
lean_object* x_18; 
x_18 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_5 = x_16;
x_6 = x_18;
x_13 = x_17;
goto _start;
}
block_31:
{
if (x_21 == 0)
{
x_16 = x_5;
x_17 = x_13;
goto block_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_nat_sub(x_1, x_6);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_25 = l_Lean_Expr_getRevArg_x21(x_2, x_24);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_26 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unbox_uint64(x_27);
lean_dec(x_27);
x_30 = lean_uint64_mix_hash(x_5, x_29);
x_16 = x_30;
x_17 = x_28;
goto block_20;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint64_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_47; uint8_t x_48; 
x_47 = lean_st_ref_get(x_3, x_8);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_49);
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_52; uint8_t x_53; 
lean_free_object(x_47);
lean_inc(x_1);
x_52 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_50);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_expr_eqv(x_54, x_1);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_52);
x_57 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint64_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox_uint64(x_58);
lean_dec(x_58);
x_36 = x_60;
x_37 = x_3;
x_38 = x_59;
goto block_46;
}
else
{
lean_dec(x_1);
return x_57;
}
}
else
{
uint64_t x_61; lean_object* x_62; 
lean_dec(x_54);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_62 = lean_box_uint64(x_61);
lean_ctor_set(x_52, 0, x_62);
return x_52;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_expr_eqv(x_63, x_1);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint64_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox_uint64(x_67);
lean_dec(x_67);
x_36 = x_69;
x_37 = x_3;
x_38 = x_68;
goto block_46;
}
else
{
lean_dec(x_1);
return x_66;
}
}
else
{
uint64_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_71 = lean_box_uint64(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
return x_72;
}
}
}
case 4:
{
lean_object* x_73; uint64_t x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = l_Lean_Name_hash___override(x_73);
lean_dec(x_73);
x_75 = lean_box_uint64(x_74);
lean_ctor_set(x_47, 0, x_75);
return x_47;
}
case 5:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_112; 
lean_free_object(x_47);
x_76 = l_Lean_Expr_getAppFn(x_1);
x_112 = l_Lean_Expr_isMVar(x_76);
if (x_112 == 0)
{
x_95 = x_2;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_50;
goto block_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_inc(x_1);
x_113 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_50);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_expr_eqv(x_114, x_1);
if (x_116 == 0)
{
lean_dec(x_76);
lean_dec(x_1);
x_1 = x_114;
x_8 = x_115;
goto _start;
}
else
{
lean_dec(x_114);
x_95 = x_2;
x_96 = x_3;
x_97 = x_4;
x_98 = x_5;
x_99 = x_6;
x_100 = x_7;
x_101 = x_115;
goto block_111;
}
}
block_94:
{
lean_object* x_85; 
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_85 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_76, x_78, x_79, x_80, x_81, x_82, x_83, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Expr_getAppNumArgs(x_1);
x_90 = lean_unsigned_to_nat(1u);
lean_inc(x_89);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_unbox_uint64(x_86);
lean_dec(x_86);
x_93 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_89, x_1, x_77, x_91, x_92, x_88, x_78, x_79, x_80, x_81, x_82, x_83, x_87);
lean_dec(x_91);
lean_dec(x_77);
lean_dec(x_1);
lean_dec(x_89);
return x_93;
}
else
{
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_1);
return x_85;
}
}
block_111:
{
uint8_t x_102; 
x_102 = l_Lean_Expr_hasLooseBVars(x_76);
if (x_102 == 0)
{
lean_object* x_103; 
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_76);
x_103 = l_Lean_Meta_getFunInfo(x_76, x_97, x_98, x_99, x_100, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_77 = x_104;
x_78 = x_95;
x_79 = x_96;
x_80 = x_97;
x_81 = x_98;
x_82 = x_99;
x_83 = x_100;
x_84 = x_105;
goto block_94;
}
else
{
uint8_t x_106; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_76);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; 
x_110 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1;
x_77 = x_110;
x_78 = x_95;
x_79 = x_96;
x_80 = x_97;
x_81 = x_98;
x_82 = x_99;
x_83 = x_100;
x_84 = x_101;
goto block_94;
}
}
}
case 6:
{
lean_object* x_118; lean_object* x_119; 
lean_free_object(x_47);
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 2);
lean_inc(x_119);
lean_dec(x_1);
x_9 = x_118;
x_10 = x_119;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_50;
goto block_35;
}
case 7:
{
lean_object* x_120; lean_object* x_121; 
lean_free_object(x_47);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 2);
lean_inc(x_121);
lean_dec(x_1);
x_9 = x_120;
x_10 = x_121;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_50;
goto block_35;
}
case 8:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_free_object(x_47);
x_122 = lean_ctor_get(x_1, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_1, 3);
lean_inc(x_123);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_124 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_123, x_2, x_3, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_131 = lean_unbox_uint64(x_129);
lean_dec(x_129);
x_132 = lean_uint64_mix_hash(x_130, x_131);
x_133 = lean_box_uint64(x_132);
lean_ctor_set(x_127, 0, x_133);
return x_127;
}
else
{
lean_object* x_134; lean_object* x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_127, 0);
x_135 = lean_ctor_get(x_127, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_127);
x_136 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_137 = lean_unbox_uint64(x_134);
lean_dec(x_134);
x_138 = lean_uint64_mix_hash(x_136, x_137);
x_139 = lean_box_uint64(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
}
else
{
lean_dec(x_125);
return x_127;
}
}
else
{
lean_dec(x_123);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_124;
}
}
case 10:
{
lean_object* x_141; lean_object* x_142; 
lean_free_object(x_47);
x_141 = lean_ctor_get(x_1, 1);
lean_inc(x_141);
x_142 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint64_t x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_unbox_uint64(x_143);
lean_dec(x_143);
x_36 = x_145;
x_37 = x_3;
x_38 = x_144;
goto block_46;
}
else
{
lean_dec(x_1);
return x_142;
}
}
case 11:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_free_object(x_47);
x_146 = lean_ctor_get(x_1, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_1, 2);
lean_inc(x_147);
lean_dec(x_1);
x_148 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_uint64_of_nat(x_146);
lean_dec(x_146);
x_152 = lean_unbox_uint64(x_150);
lean_dec(x_150);
x_153 = lean_uint64_mix_hash(x_151, x_152);
x_154 = lean_box_uint64(x_153);
lean_ctor_set(x_148, 0, x_154);
return x_148;
}
else
{
lean_object* x_155; lean_object* x_156; uint64_t x_157; uint64_t x_158; uint64_t x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_148, 0);
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_148);
x_157 = lean_uint64_of_nat(x_146);
lean_dec(x_146);
x_158 = lean_unbox_uint64(x_155);
lean_dec(x_155);
x_159 = lean_uint64_mix_hash(x_157, x_158);
x_160 = lean_box_uint64(x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_156);
return x_161;
}
}
else
{
lean_dec(x_146);
return x_148;
}
}
default: 
{
uint64_t x_162; lean_object* x_163; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_162 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_163 = lean_box_uint64(x_162);
lean_ctor_set(x_47, 0, x_163);
return x_47;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_164 = lean_ctor_get(x_51, 0);
lean_inc(x_164);
lean_dec(x_51);
lean_ctor_set(x_47, 0, x_164);
return x_47;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_47, 0);
x_166 = lean_ctor_get(x_47, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_47);
x_167 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__1(x_1, x_165);
lean_dec(x_165);
if (lean_obj_tag(x_167) == 0)
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_inc(x_1);
x_168 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_expr_eqv(x_169, x_1);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_171);
x_173 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_170);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint64_t x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_unbox_uint64(x_174);
lean_dec(x_174);
x_36 = x_176;
x_37 = x_3;
x_38 = x_175;
goto block_46;
}
else
{
lean_dec(x_1);
return x_173;
}
}
else
{
uint64_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_169);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_178 = lean_box_uint64(x_177);
if (lean_is_scalar(x_171)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_171;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_170);
return x_179;
}
}
case 4:
{
lean_object* x_180; uint64_t x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_180 = lean_ctor_get(x_1, 0);
lean_inc(x_180);
lean_dec(x_1);
x_181 = l_Lean_Name_hash___override(x_180);
lean_dec(x_180);
x_182 = lean_box_uint64(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_166);
return x_183;
}
case 5:
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_220; 
x_184 = l_Lean_Expr_getAppFn(x_1);
x_220 = l_Lean_Expr_isMVar(x_184);
if (x_220 == 0)
{
x_203 = x_2;
x_204 = x_3;
x_205 = x_4;
x_206 = x_5;
x_207 = x_6;
x_208 = x_7;
x_209 = x_166;
goto block_219;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_inc(x_1);
x_221 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_5, x_166);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_expr_eqv(x_222, x_1);
if (x_224 == 0)
{
lean_dec(x_184);
lean_dec(x_1);
x_1 = x_222;
x_8 = x_223;
goto _start;
}
else
{
lean_dec(x_222);
x_203 = x_2;
x_204 = x_3;
x_205 = x_4;
x_206 = x_5;
x_207 = x_6;
x_208 = x_7;
x_209 = x_223;
goto block_219;
}
}
block_202:
{
lean_object* x_193; 
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
x_193 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_184, x_186, x_187, x_188, x_189, x_190, x_191, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_unsigned_to_nat(0u);
x_197 = l_Lean_Expr_getAppNumArgs(x_1);
x_198 = lean_unsigned_to_nat(1u);
lean_inc(x_197);
x_199 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_198);
x_200 = lean_unbox_uint64(x_194);
lean_dec(x_194);
x_201 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_197, x_1, x_185, x_199, x_200, x_196, x_186, x_187, x_188, x_189, x_190, x_191, x_195);
lean_dec(x_199);
lean_dec(x_185);
lean_dec(x_1);
lean_dec(x_197);
return x_201;
}
else
{
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_1);
return x_193;
}
}
block_219:
{
uint8_t x_210; 
x_210 = l_Lean_Expr_hasLooseBVars(x_184);
if (x_210 == 0)
{
lean_object* x_211; 
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_184);
x_211 = l_Lean_Meta_getFunInfo(x_184, x_205, x_206, x_207, x_208, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_185 = x_212;
x_186 = x_203;
x_187 = x_204;
x_188 = x_205;
x_189 = x_206;
x_190 = x_207;
x_191 = x_208;
x_192 = x_213;
goto block_202;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_184);
lean_dec(x_1);
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; 
x_218 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1;
x_185 = x_218;
x_186 = x_203;
x_187 = x_204;
x_188 = x_205;
x_189 = x_206;
x_190 = x_207;
x_191 = x_208;
x_192 = x_209;
goto block_202;
}
}
}
case 6:
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_1, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_1, 2);
lean_inc(x_227);
lean_dec(x_1);
x_9 = x_226;
x_10 = x_227;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_166;
goto block_35;
}
case 7:
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_1, 2);
lean_inc(x_229);
lean_dec(x_1);
x_9 = x_228;
x_10 = x_229;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_166;
goto block_35;
}
case 8:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_1, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_1, 3);
lean_inc(x_231);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_232 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_230, x_2, x_3, x_4, x_5, x_6, x_7, x_166);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint64_t x_239; uint64_t x_240; uint64_t x_241; lean_object* x_242; lean_object* x_243; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_unbox_uint64(x_233);
lean_dec(x_233);
x_240 = lean_unbox_uint64(x_236);
lean_dec(x_236);
x_241 = lean_uint64_mix_hash(x_239, x_240);
x_242 = lean_box_uint64(x_241);
if (lean_is_scalar(x_238)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_238;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_237);
return x_243;
}
else
{
lean_dec(x_233);
return x_235;
}
}
else
{
lean_dec(x_231);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_232;
}
}
case 10:
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_1, 1);
lean_inc(x_244);
x_245 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_244, x_2, x_3, x_4, x_5, x_6, x_7, x_166);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint64_t x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_unbox_uint64(x_246);
lean_dec(x_246);
x_36 = x_248;
x_37 = x_3;
x_38 = x_247;
goto block_46;
}
else
{
lean_dec(x_1);
return x_245;
}
}
case 11:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_1, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_1, 2);
lean_inc(x_250);
lean_dec(x_1);
x_251 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_250, x_2, x_3, x_4, x_5, x_6, x_7, x_166);
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
x_255 = lean_uint64_of_nat(x_249);
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
lean_dec(x_249);
return x_251;
}
}
default: 
{
uint64_t x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_260 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_261 = lean_box_uint64(x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_166);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_263 = lean_ctor_get(x_167, 0);
lean_inc(x_263);
lean_dec(x_167);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_166);
return x_264;
}
}
block_35:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_18 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_9, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_unbox_uint64(x_19);
lean_dec(x_19);
x_25 = lean_unbox_uint64(x_23);
lean_dec(x_23);
x_26 = lean_uint64_mix_hash(x_24, x_25);
x_27 = lean_box_uint64(x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_unbox_uint64(x_19);
lean_dec(x_19);
x_31 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = lean_box_uint64(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
lean_dec(x_19);
return x_21;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
return x_18;
}
}
block_46:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_unsafe__8___redArg(x_1, x_36, x_37, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box_uint64(x_36);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box_uint64(x_36);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint64_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___redArg(x_1, x_2, x_3, x_4, x_14, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint64_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey_spec__1(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(x_2, x_3);
return x_4;
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
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(x_1, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_Canonicalizer_canon_unsafe__1_spec__0(x_1, x_4, x_3);
return x_5;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_8 = lean_uint64_dec_eq(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_unbox_uint64(x_5);
x_9 = lean_uint64_dec_eq(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_box_uint64(x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_unbox_uint64(x_12);
x_16 = lean_uint64_dec_eq(x_15, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_1, x_2, x_14);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
x_19 = lean_box_uint64(x_1);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
lean_inc(x_1);
x_15 = l_Lean_Meta_isExprDefEq(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_4);
lean_dec(x_13);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_2);
{
lean_object* _tmp_3 = x_14;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_9 = x_18;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_22);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
lean_inc(x_1);
x_32 = l_Lean_Meta_isExprDefEq(x_1, x_30, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
lean_inc(x_2);
{
lean_object* _tmp_3 = x_31;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_9 = x_35;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_30);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_44 = x_32;
} else {
 lean_dec_ref(x_32);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_2, x_3, x_5, x_6, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Canonicalizer_canon___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
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
lean_object* x_17; uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_st_ref_take(x_3, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_32; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint64_t x_51; uint8_t x_52; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
x_35 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_35);
lean_ctor_set(x_17, 0, x_1);
x_36 = lean_array_get_size(x_34);
x_37 = 32;
x_38 = lean_unbox_uint64(x_10);
x_39 = lean_uint64_shift_right(x_38, x_37);
x_40 = lean_unbox_uint64(x_10);
x_41 = lean_uint64_xor(x_40, x_39);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_34, x_49);
x_51 = lean_unbox_uint64(x_10);
lean_inc(x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_33, x_53);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_17);
lean_ctor_set(x_55, 2, x_50);
x_56 = lean_array_uset(x_34, x_49, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_56);
lean_ctor_set(x_22, 1, x_63);
lean_ctor_set(x_22, 0, x_54);
x_24 = x_22;
goto block_31;
}
else
{
lean_ctor_set(x_22, 1, x_56);
lean_ctor_set(x_22, 0, x_54);
x_24 = x_22;
goto block_31;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = lean_array_uset(x_34, x_49, x_64);
x_66 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_67 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_66, x_17, x_50);
x_68 = lean_array_uset(x_65, x_49, x_67);
lean_ctor_set(x_22, 1, x_68);
x_24 = x_22;
goto block_31;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint64_t x_87; uint8_t x_88; 
x_69 = lean_ctor_get(x_22, 0);
x_70 = lean_ctor_get(x_22, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_22);
x_71 = lean_box(0);
lean_inc(x_1);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_71);
lean_ctor_set(x_17, 0, x_1);
x_72 = lean_array_get_size(x_70);
x_73 = 32;
x_74 = lean_unbox_uint64(x_10);
x_75 = lean_uint64_shift_right(x_74, x_73);
x_76 = lean_unbox_uint64(x_10);
x_77 = lean_uint64_xor(x_76, x_75);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_70, x_85);
x_87 = lean_unbox_uint64(x_10);
lean_inc(x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_87, x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_69, x_89);
lean_dec(x_69);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_10);
lean_ctor_set(x_91, 1, x_17);
lean_ctor_set(x_91, 2, x_86);
x_92 = lean_array_uset(x_70, x_85, x_91);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_mul(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_24 = x_100;
goto block_31;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
x_24 = x_101;
goto block_31;
}
}
else
{
lean_object* x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_70, x_85, x_102);
x_104 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_105 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_104, x_17, x_86);
x_106 = lean_array_uset(x_103, x_85, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_69);
lean_ctor_set(x_107, 1, x_106);
x_24 = x_107;
goto block_31;
}
}
block_31:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_st_ref_set(x_3, x_25, x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; size_t x_134; size_t x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; uint64_t x_140; uint8_t x_141; 
x_108 = lean_ctor_get(x_17, 0);
x_109 = lean_ctor_get(x_17, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_17);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_111, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_122 = x_111;
} else {
 lean_dec_ref(x_111);
 x_122 = lean_box(0);
}
x_123 = lean_box(0);
lean_inc(x_1);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_get_size(x_121);
x_126 = 32;
x_127 = lean_unbox_uint64(x_10);
x_128 = lean_uint64_shift_right(x_127, x_126);
x_129 = lean_unbox_uint64(x_10);
x_130 = lean_uint64_xor(x_129, x_128);
x_131 = 16;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = lean_uint64_to_usize(x_133);
x_135 = lean_usize_of_nat(x_125);
lean_dec(x_125);
x_136 = 1;
x_137 = lean_usize_sub(x_135, x_136);
x_138 = lean_usize_land(x_134, x_137);
x_139 = lean_array_uget(x_121, x_138);
x_140 = lean_unbox_uint64(x_10);
lean_inc(x_139);
x_141 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_140, x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_120, x_142);
lean_dec(x_120);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_10);
lean_ctor_set(x_144, 1, x_124);
lean_ctor_set(x_144, 2, x_139);
x_145 = lean_array_uset(x_121, x_138, x_144);
x_146 = lean_unsigned_to_nat(4u);
x_147 = lean_nat_mul(x_143, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_145);
if (lean_is_scalar(x_122)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_122;
}
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_113 = x_153;
goto block_119;
}
else
{
lean_object* x_154; 
if (lean_is_scalar(x_122)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_122;
}
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_145);
x_113 = x_154;
goto block_119;
}
}
else
{
lean_object* x_155; lean_object* x_156; uint64_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_box(0);
x_156 = lean_array_uset(x_121, x_138, x_155);
x_157 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_158 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_157, x_124, x_139);
x_159 = lean_array_uset(x_156, x_138, x_158);
if (lean_is_scalar(x_122)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_122;
}
lean_ctor_set(x_160, 0, x_120);
lean_ctor_set(x_160, 1, x_159);
x_113 = x_160;
goto block_119;
}
block_119:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_st_ref_set(x_3, x_114, x_109);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_4, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_16, 0);
lean_inc(x_162);
lean_dec(x_16);
x_163 = !lean_is_exclusive(x_4);
if (x_163 == 0)
{
uint64_t x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_165 = lean_ctor_get(x_4, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_161);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; lean_object* x_174; 
x_167 = lean_box(0);
x_168 = l_Lean_Meta_Canonicalizer_canon___closed__0;
lean_ctor_set_uint8(x_161, 9, x_2);
x_169 = 2;
x_170 = lean_uint64_shift_right(x_164, x_169);
x_171 = lean_uint64_shift_left(x_170, x_169);
x_172 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_173 = lean_uint64_lor(x_171, x_172);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_173);
lean_inc(x_162);
lean_inc(x_1);
x_174 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_168, x_167, x_162, x_168, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec(x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_st_ref_take(x_3, x_177);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_193; 
x_180 = lean_ctor_get(x_178, 0);
x_181 = lean_ctor_get(x_178, 1);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_184 = x_180;
} else {
 lean_dec_ref(x_180);
 x_184 = lean_box(0);
}
x_193 = !lean_is_exclusive(x_183);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; uint64_t x_201; uint64_t x_202; uint64_t x_203; uint64_t x_204; size_t x_205; size_t x_206; size_t x_207; size_t x_208; size_t x_209; lean_object* x_210; uint64_t x_211; uint8_t x_212; 
x_194 = lean_ctor_get(x_183, 0);
x_195 = lean_ctor_get(x_183, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_178, 1);
lean_ctor_set(x_178, 1, x_162);
lean_ctor_set(x_178, 0, x_1);
x_196 = lean_array_get_size(x_195);
x_197 = 32;
x_198 = lean_unbox_uint64(x_10);
x_199 = lean_uint64_shift_right(x_198, x_197);
x_200 = lean_unbox_uint64(x_10);
x_201 = lean_uint64_xor(x_200, x_199);
x_202 = 16;
x_203 = lean_uint64_shift_right(x_201, x_202);
x_204 = lean_uint64_xor(x_201, x_203);
x_205 = lean_uint64_to_usize(x_204);
x_206 = lean_usize_of_nat(x_196);
lean_dec(x_196);
x_207 = 1;
x_208 = lean_usize_sub(x_206, x_207);
x_209 = lean_usize_land(x_205, x_208);
x_210 = lean_array_uget(x_195, x_209);
x_211 = lean_unbox_uint64(x_10);
lean_inc(x_210);
x_212 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_211, x_210);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_194, x_213);
lean_dec(x_194);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_10);
lean_ctor_set(x_215, 1, x_178);
lean_ctor_set(x_215, 2, x_210);
x_216 = lean_array_uset(x_195, x_209, x_215);
x_217 = lean_unsigned_to_nat(4u);
x_218 = lean_nat_mul(x_214, x_217);
x_219 = lean_unsigned_to_nat(3u);
x_220 = lean_nat_div(x_218, x_219);
lean_dec(x_218);
x_221 = lean_array_get_size(x_216);
x_222 = lean_nat_dec_le(x_220, x_221);
lean_dec(x_221);
lean_dec(x_220);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_216);
lean_ctor_set(x_183, 1, x_223);
lean_ctor_set(x_183, 0, x_214);
x_185 = x_183;
goto block_192;
}
else
{
lean_ctor_set(x_183, 1, x_216);
lean_ctor_set(x_183, 0, x_214);
x_185 = x_183;
goto block_192;
}
}
else
{
lean_object* x_224; lean_object* x_225; uint64_t x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_box(0);
x_225 = lean_array_uset(x_195, x_209, x_224);
x_226 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_227 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_226, x_178, x_210);
x_228 = lean_array_uset(x_225, x_209, x_227);
lean_ctor_set(x_183, 1, x_228);
x_185 = x_183;
goto block_192;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; size_t x_240; size_t x_241; size_t x_242; size_t x_243; size_t x_244; lean_object* x_245; uint64_t x_246; uint8_t x_247; 
x_229 = lean_ctor_get(x_183, 0);
x_230 = lean_ctor_get(x_183, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_183);
lean_inc(x_1);
lean_ctor_set_tag(x_178, 1);
lean_ctor_set(x_178, 1, x_162);
lean_ctor_set(x_178, 0, x_1);
x_231 = lean_array_get_size(x_230);
x_232 = 32;
x_233 = lean_unbox_uint64(x_10);
x_234 = lean_uint64_shift_right(x_233, x_232);
x_235 = lean_unbox_uint64(x_10);
x_236 = lean_uint64_xor(x_235, x_234);
x_237 = 16;
x_238 = lean_uint64_shift_right(x_236, x_237);
x_239 = lean_uint64_xor(x_236, x_238);
x_240 = lean_uint64_to_usize(x_239);
x_241 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_242 = 1;
x_243 = lean_usize_sub(x_241, x_242);
x_244 = lean_usize_land(x_240, x_243);
x_245 = lean_array_uget(x_230, x_244);
x_246 = lean_unbox_uint64(x_10);
lean_inc(x_245);
x_247 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_246, x_245);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_nat_add(x_229, x_248);
lean_dec(x_229);
x_250 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_250, 0, x_10);
lean_ctor_set(x_250, 1, x_178);
lean_ctor_set(x_250, 2, x_245);
x_251 = lean_array_uset(x_230, x_244, x_250);
x_252 = lean_unsigned_to_nat(4u);
x_253 = lean_nat_mul(x_249, x_252);
x_254 = lean_unsigned_to_nat(3u);
x_255 = lean_nat_div(x_253, x_254);
lean_dec(x_253);
x_256 = lean_array_get_size(x_251);
x_257 = lean_nat_dec_le(x_255, x_256);
lean_dec(x_256);
lean_dec(x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_251);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_249);
lean_ctor_set(x_259, 1, x_258);
x_185 = x_259;
goto block_192;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_249);
lean_ctor_set(x_260, 1, x_251);
x_185 = x_260;
goto block_192;
}
}
else
{
lean_object* x_261; lean_object* x_262; uint64_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_box(0);
x_262 = lean_array_uset(x_230, x_244, x_261);
x_263 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_264 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_263, x_178, x_245);
x_265 = lean_array_uset(x_262, x_244, x_264);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_229);
lean_ctor_set(x_266, 1, x_265);
x_185 = x_266;
goto block_192;
}
}
block_192:
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_st_ref_set(x_3, x_186, x_181);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 0);
lean_dec(x_189);
lean_ctor_set(x_187, 0, x_1);
return x_187;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_1);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint64_t x_284; uint64_t x_285; uint64_t x_286; uint64_t x_287; uint64_t x_288; uint64_t x_289; uint64_t x_290; uint64_t x_291; size_t x_292; size_t x_293; size_t x_294; size_t x_295; size_t x_296; lean_object* x_297; uint64_t x_298; uint8_t x_299; 
x_267 = lean_ctor_get(x_178, 0);
x_268 = lean_ctor_get(x_178, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_178);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
x_279 = lean_ctor_get(x_270, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_270, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_281 = x_270;
} else {
 lean_dec_ref(x_270);
 x_281 = lean_box(0);
}
lean_inc(x_1);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_162);
x_283 = lean_array_get_size(x_280);
x_284 = 32;
x_285 = lean_unbox_uint64(x_10);
x_286 = lean_uint64_shift_right(x_285, x_284);
x_287 = lean_unbox_uint64(x_10);
x_288 = lean_uint64_xor(x_287, x_286);
x_289 = 16;
x_290 = lean_uint64_shift_right(x_288, x_289);
x_291 = lean_uint64_xor(x_288, x_290);
x_292 = lean_uint64_to_usize(x_291);
x_293 = lean_usize_of_nat(x_283);
lean_dec(x_283);
x_294 = 1;
x_295 = lean_usize_sub(x_293, x_294);
x_296 = lean_usize_land(x_292, x_295);
x_297 = lean_array_uget(x_280, x_296);
x_298 = lean_unbox_uint64(x_10);
lean_inc(x_297);
x_299 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_298, x_297);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_300 = lean_unsigned_to_nat(1u);
x_301 = lean_nat_add(x_279, x_300);
lean_dec(x_279);
x_302 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_302, 0, x_10);
lean_ctor_set(x_302, 1, x_282);
lean_ctor_set(x_302, 2, x_297);
x_303 = lean_array_uset(x_280, x_296, x_302);
x_304 = lean_unsigned_to_nat(4u);
x_305 = lean_nat_mul(x_301, x_304);
x_306 = lean_unsigned_to_nat(3u);
x_307 = lean_nat_div(x_305, x_306);
lean_dec(x_305);
x_308 = lean_array_get_size(x_303);
x_309 = lean_nat_dec_le(x_307, x_308);
lean_dec(x_308);
lean_dec(x_307);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_303);
if (lean_is_scalar(x_281)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_281;
}
lean_ctor_set(x_311, 0, x_301);
lean_ctor_set(x_311, 1, x_310);
x_272 = x_311;
goto block_278;
}
else
{
lean_object* x_312; 
if (lean_is_scalar(x_281)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_281;
}
lean_ctor_set(x_312, 0, x_301);
lean_ctor_set(x_312, 1, x_303);
x_272 = x_312;
goto block_278;
}
}
else
{
lean_object* x_313; lean_object* x_314; uint64_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_313 = lean_box(0);
x_314 = lean_array_uset(x_280, x_296, x_313);
x_315 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_316 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_315, x_282, x_297);
x_317 = lean_array_uset(x_314, x_296, x_316);
if (lean_is_scalar(x_281)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_281;
}
lean_ctor_set(x_318, 0, x_279);
lean_ctor_set(x_318, 1, x_317);
x_272 = x_318;
goto block_278;
}
block_278:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_269);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_st_ref_set(x_3, x_273, x_268);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_1);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_162);
lean_dec(x_10);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_174);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_174, 0);
lean_dec(x_320);
x_321 = lean_ctor_get(x_176, 0);
lean_inc(x_321);
lean_dec(x_176);
lean_ctor_set(x_174, 0, x_321);
return x_174;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_174, 1);
lean_inc(x_322);
lean_dec(x_174);
x_323 = lean_ctor_get(x_176, 0);
lean_inc(x_323);
lean_dec(x_176);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_162);
lean_dec(x_10);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_174);
if (x_325 == 0)
{
return x_174;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_174, 0);
x_327 = lean_ctor_get(x_174, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_174);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; uint8_t x_335; uint8_t x_336; uint8_t x_337; uint8_t x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint64_t x_349; uint64_t x_350; uint64_t x_351; uint64_t x_352; uint64_t x_353; lean_object* x_354; 
x_329 = lean_ctor_get_uint8(x_161, 0);
x_330 = lean_ctor_get_uint8(x_161, 1);
x_331 = lean_ctor_get_uint8(x_161, 2);
x_332 = lean_ctor_get_uint8(x_161, 3);
x_333 = lean_ctor_get_uint8(x_161, 4);
x_334 = lean_ctor_get_uint8(x_161, 5);
x_335 = lean_ctor_get_uint8(x_161, 6);
x_336 = lean_ctor_get_uint8(x_161, 7);
x_337 = lean_ctor_get_uint8(x_161, 8);
x_338 = lean_ctor_get_uint8(x_161, 10);
x_339 = lean_ctor_get_uint8(x_161, 11);
x_340 = lean_ctor_get_uint8(x_161, 12);
x_341 = lean_ctor_get_uint8(x_161, 13);
x_342 = lean_ctor_get_uint8(x_161, 14);
x_343 = lean_ctor_get_uint8(x_161, 15);
x_344 = lean_ctor_get_uint8(x_161, 16);
x_345 = lean_ctor_get_uint8(x_161, 17);
lean_dec(x_161);
x_346 = lean_box(0);
x_347 = l_Lean_Meta_Canonicalizer_canon___closed__0;
x_348 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_348, 0, x_329);
lean_ctor_set_uint8(x_348, 1, x_330);
lean_ctor_set_uint8(x_348, 2, x_331);
lean_ctor_set_uint8(x_348, 3, x_332);
lean_ctor_set_uint8(x_348, 4, x_333);
lean_ctor_set_uint8(x_348, 5, x_334);
lean_ctor_set_uint8(x_348, 6, x_335);
lean_ctor_set_uint8(x_348, 7, x_336);
lean_ctor_set_uint8(x_348, 8, x_337);
lean_ctor_set_uint8(x_348, 9, x_2);
lean_ctor_set_uint8(x_348, 10, x_338);
lean_ctor_set_uint8(x_348, 11, x_339);
lean_ctor_set_uint8(x_348, 12, x_340);
lean_ctor_set_uint8(x_348, 13, x_341);
lean_ctor_set_uint8(x_348, 14, x_342);
lean_ctor_set_uint8(x_348, 15, x_343);
lean_ctor_set_uint8(x_348, 16, x_344);
lean_ctor_set_uint8(x_348, 17, x_345);
x_349 = 2;
x_350 = lean_uint64_shift_right(x_164, x_349);
x_351 = lean_uint64_shift_left(x_350, x_349);
x_352 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_353 = lean_uint64_lor(x_351, x_352);
lean_ctor_set(x_4, 0, x_348);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_353);
lean_inc(x_162);
lean_inc(x_1);
x_354 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_347, x_346, x_162, x_347, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec(x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint64_t x_377; uint64_t x_378; uint64_t x_379; uint64_t x_380; uint64_t x_381; uint64_t x_382; uint64_t x_383; uint64_t x_384; size_t x_385; size_t x_386; size_t x_387; size_t x_388; size_t x_389; lean_object* x_390; uint64_t x_391; uint8_t x_392; 
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_st_ref_take(x_3, x_357);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_361 = x_358;
} else {
 lean_dec_ref(x_358);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_364 = x_359;
} else {
 lean_dec_ref(x_359);
 x_364 = lean_box(0);
}
x_372 = lean_ctor_get(x_363, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_363, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_374 = x_363;
} else {
 lean_dec_ref(x_363);
 x_374 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_361)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_361;
 lean_ctor_set_tag(x_375, 1);
}
lean_ctor_set(x_375, 0, x_1);
lean_ctor_set(x_375, 1, x_162);
x_376 = lean_array_get_size(x_373);
x_377 = 32;
x_378 = lean_unbox_uint64(x_10);
x_379 = lean_uint64_shift_right(x_378, x_377);
x_380 = lean_unbox_uint64(x_10);
x_381 = lean_uint64_xor(x_380, x_379);
x_382 = 16;
x_383 = lean_uint64_shift_right(x_381, x_382);
x_384 = lean_uint64_xor(x_381, x_383);
x_385 = lean_uint64_to_usize(x_384);
x_386 = lean_usize_of_nat(x_376);
lean_dec(x_376);
x_387 = 1;
x_388 = lean_usize_sub(x_386, x_387);
x_389 = lean_usize_land(x_385, x_388);
x_390 = lean_array_uget(x_373, x_389);
x_391 = lean_unbox_uint64(x_10);
lean_inc(x_390);
x_392 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_391, x_390);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_393 = lean_unsigned_to_nat(1u);
x_394 = lean_nat_add(x_372, x_393);
lean_dec(x_372);
x_395 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_395, 0, x_10);
lean_ctor_set(x_395, 1, x_375);
lean_ctor_set(x_395, 2, x_390);
x_396 = lean_array_uset(x_373, x_389, x_395);
x_397 = lean_unsigned_to_nat(4u);
x_398 = lean_nat_mul(x_394, x_397);
x_399 = lean_unsigned_to_nat(3u);
x_400 = lean_nat_div(x_398, x_399);
lean_dec(x_398);
x_401 = lean_array_get_size(x_396);
x_402 = lean_nat_dec_le(x_400, x_401);
lean_dec(x_401);
lean_dec(x_400);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_396);
if (lean_is_scalar(x_374)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_374;
}
lean_ctor_set(x_404, 0, x_394);
lean_ctor_set(x_404, 1, x_403);
x_365 = x_404;
goto block_371;
}
else
{
lean_object* x_405; 
if (lean_is_scalar(x_374)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_374;
}
lean_ctor_set(x_405, 0, x_394);
lean_ctor_set(x_405, 1, x_396);
x_365 = x_405;
goto block_371;
}
}
else
{
lean_object* x_406; lean_object* x_407; uint64_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_box(0);
x_407 = lean_array_uset(x_373, x_389, x_406);
x_408 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_409 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_408, x_375, x_390);
x_410 = lean_array_uset(x_407, x_389, x_409);
if (lean_is_scalar(x_374)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_374;
}
lean_ctor_set(x_411, 0, x_372);
lean_ctor_set(x_411, 1, x_410);
x_365 = x_411;
goto block_371;
}
block_371:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_364;
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_st_ref_set(x_3, x_366, x_360);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_369 = x_367;
} else {
 lean_dec_ref(x_367);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_1);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_162);
lean_dec(x_10);
lean_dec(x_1);
x_412 = lean_ctor_get(x_354, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_413 = x_354;
} else {
 lean_dec_ref(x_354);
 x_413 = lean_box(0);
}
x_414 = lean_ctor_get(x_356, 0);
lean_inc(x_414);
lean_dec(x_356);
if (lean_is_scalar(x_413)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_413;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_412);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_162);
lean_dec(x_10);
lean_dec(x_1);
x_416 = lean_ctor_get(x_354, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_354, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_418 = x_354;
} else {
 lean_dec_ref(x_354);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
return x_419;
}
}
}
else
{
uint64_t x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; uint8_t x_435; uint8_t x_436; uint8_t x_437; uint8_t x_438; uint8_t x_439; uint8_t x_440; uint8_t x_441; uint8_t x_442; uint8_t x_443; uint8_t x_444; uint8_t x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint64_t x_451; uint64_t x_452; uint64_t x_453; uint64_t x_454; uint64_t x_455; lean_object* x_456; lean_object* x_457; 
x_420 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_421 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_422 = lean_ctor_get(x_4, 1);
x_423 = lean_ctor_get(x_4, 2);
x_424 = lean_ctor_get(x_4, 3);
x_425 = lean_ctor_get(x_4, 4);
x_426 = lean_ctor_get(x_4, 5);
x_427 = lean_ctor_get(x_4, 6);
x_428 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_429 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_427);
lean_inc(x_426);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_4);
x_430 = lean_ctor_get_uint8(x_161, 0);
x_431 = lean_ctor_get_uint8(x_161, 1);
x_432 = lean_ctor_get_uint8(x_161, 2);
x_433 = lean_ctor_get_uint8(x_161, 3);
x_434 = lean_ctor_get_uint8(x_161, 4);
x_435 = lean_ctor_get_uint8(x_161, 5);
x_436 = lean_ctor_get_uint8(x_161, 6);
x_437 = lean_ctor_get_uint8(x_161, 7);
x_438 = lean_ctor_get_uint8(x_161, 8);
x_439 = lean_ctor_get_uint8(x_161, 10);
x_440 = lean_ctor_get_uint8(x_161, 11);
x_441 = lean_ctor_get_uint8(x_161, 12);
x_442 = lean_ctor_get_uint8(x_161, 13);
x_443 = lean_ctor_get_uint8(x_161, 14);
x_444 = lean_ctor_get_uint8(x_161, 15);
x_445 = lean_ctor_get_uint8(x_161, 16);
x_446 = lean_ctor_get_uint8(x_161, 17);
if (lean_is_exclusive(x_161)) {
 x_447 = x_161;
} else {
 lean_dec_ref(x_161);
 x_447 = lean_box(0);
}
x_448 = lean_box(0);
x_449 = l_Lean_Meta_Canonicalizer_canon___closed__0;
if (lean_is_scalar(x_447)) {
 x_450 = lean_alloc_ctor(0, 0, 18);
} else {
 x_450 = x_447;
}
lean_ctor_set_uint8(x_450, 0, x_430);
lean_ctor_set_uint8(x_450, 1, x_431);
lean_ctor_set_uint8(x_450, 2, x_432);
lean_ctor_set_uint8(x_450, 3, x_433);
lean_ctor_set_uint8(x_450, 4, x_434);
lean_ctor_set_uint8(x_450, 5, x_435);
lean_ctor_set_uint8(x_450, 6, x_436);
lean_ctor_set_uint8(x_450, 7, x_437);
lean_ctor_set_uint8(x_450, 8, x_438);
lean_ctor_set_uint8(x_450, 9, x_2);
lean_ctor_set_uint8(x_450, 10, x_439);
lean_ctor_set_uint8(x_450, 11, x_440);
lean_ctor_set_uint8(x_450, 12, x_441);
lean_ctor_set_uint8(x_450, 13, x_442);
lean_ctor_set_uint8(x_450, 14, x_443);
lean_ctor_set_uint8(x_450, 15, x_444);
lean_ctor_set_uint8(x_450, 16, x_445);
lean_ctor_set_uint8(x_450, 17, x_446);
x_451 = 2;
x_452 = lean_uint64_shift_right(x_420, x_451);
x_453 = lean_uint64_shift_left(x_452, x_451);
x_454 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
x_455 = lean_uint64_lor(x_453, x_454);
x_456 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_456, 0, x_450);
lean_ctor_set(x_456, 1, x_422);
lean_ctor_set(x_456, 2, x_423);
lean_ctor_set(x_456, 3, x_424);
lean_ctor_set(x_456, 4, x_425);
lean_ctor_set(x_456, 5, x_426);
lean_ctor_set(x_456, 6, x_427);
lean_ctor_set_uint64(x_456, sizeof(void*)*7, x_455);
lean_ctor_set_uint8(x_456, sizeof(void*)*7 + 8, x_421);
lean_ctor_set_uint8(x_456, sizeof(void*)*7 + 9, x_428);
lean_ctor_set_uint8(x_456, sizeof(void*)*7 + 10, x_429);
lean_inc(x_162);
lean_inc(x_1);
x_457 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___redArg(x_1, x_449, x_448, x_162, x_449, x_456, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
lean_dec(x_458);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint64_t x_480; uint64_t x_481; uint64_t x_482; uint64_t x_483; uint64_t x_484; uint64_t x_485; uint64_t x_486; uint64_t x_487; size_t x_488; size_t x_489; size_t x_490; size_t x_491; size_t x_492; lean_object* x_493; uint64_t x_494; uint8_t x_495; 
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
lean_dec(x_457);
x_461 = lean_st_ref_take(x_3, x_460);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_464 = x_461;
} else {
 lean_dec_ref(x_461);
 x_464 = lean_box(0);
}
x_465 = lean_ctor_get(x_462, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_462, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_467 = x_462;
} else {
 lean_dec_ref(x_462);
 x_467 = lean_box(0);
}
x_475 = lean_ctor_get(x_466, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_477 = x_466;
} else {
 lean_dec_ref(x_466);
 x_477 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_464)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_464;
 lean_ctor_set_tag(x_478, 1);
}
lean_ctor_set(x_478, 0, x_1);
lean_ctor_set(x_478, 1, x_162);
x_479 = lean_array_get_size(x_476);
x_480 = 32;
x_481 = lean_unbox_uint64(x_10);
x_482 = lean_uint64_shift_right(x_481, x_480);
x_483 = lean_unbox_uint64(x_10);
x_484 = lean_uint64_xor(x_483, x_482);
x_485 = 16;
x_486 = lean_uint64_shift_right(x_484, x_485);
x_487 = lean_uint64_xor(x_484, x_486);
x_488 = lean_uint64_to_usize(x_487);
x_489 = lean_usize_of_nat(x_479);
lean_dec(x_479);
x_490 = 1;
x_491 = lean_usize_sub(x_489, x_490);
x_492 = lean_usize_land(x_488, x_491);
x_493 = lean_array_uget(x_476, x_492);
x_494 = lean_unbox_uint64(x_10);
lean_inc(x_493);
x_495 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_494, x_493);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_496 = lean_unsigned_to_nat(1u);
x_497 = lean_nat_add(x_475, x_496);
lean_dec(x_475);
x_498 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_498, 0, x_10);
lean_ctor_set(x_498, 1, x_478);
lean_ctor_set(x_498, 2, x_493);
x_499 = lean_array_uset(x_476, x_492, x_498);
x_500 = lean_unsigned_to_nat(4u);
x_501 = lean_nat_mul(x_497, x_500);
x_502 = lean_unsigned_to_nat(3u);
x_503 = lean_nat_div(x_501, x_502);
lean_dec(x_501);
x_504 = lean_array_get_size(x_499);
x_505 = lean_nat_dec_le(x_503, x_504);
lean_dec(x_504);
lean_dec(x_503);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
x_506 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Meta_Canonicalizer_canon_spec__1___redArg(x_499);
if (lean_is_scalar(x_477)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_477;
}
lean_ctor_set(x_507, 0, x_497);
lean_ctor_set(x_507, 1, x_506);
x_468 = x_507;
goto block_474;
}
else
{
lean_object* x_508; 
if (lean_is_scalar(x_477)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_477;
}
lean_ctor_set(x_508, 0, x_497);
lean_ctor_set(x_508, 1, x_499);
x_468 = x_508;
goto block_474;
}
}
else
{
lean_object* x_509; lean_object* x_510; uint64_t x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_509 = lean_box(0);
x_510 = lean_array_uset(x_476, x_492, x_509);
x_511 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_512 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_511, x_478, x_493);
x_513 = lean_array_uset(x_510, x_492, x_512);
if (lean_is_scalar(x_477)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_477;
}
lean_ctor_set(x_514, 0, x_475);
lean_ctor_set(x_514, 1, x_513);
x_468 = x_514;
goto block_474;
}
block_474:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(0, 2, 0);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_465);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_st_ref_set(x_3, x_469, x_463);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_1);
lean_ctor_set(x_473, 1, x_471);
return x_473;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_162);
lean_dec(x_10);
lean_dec(x_1);
x_515 = lean_ctor_get(x_457, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_516 = x_457;
} else {
 lean_dec_ref(x_457);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_459, 0);
lean_inc(x_517);
lean_dec(x_459);
if (lean_is_scalar(x_516)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_516;
}
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_515);
return x_518;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_162);
lean_dec(x_10);
lean_dec(x_1);
x_519 = lean_ctor_get(x_457, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_457, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_521 = x_457;
} else {
 lean_dec_ref(x_457);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
return x_522;
}
}
}
}
else
{
uint8_t x_523; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_523 = !lean_is_exclusive(x_9);
if (x_523 == 0)
{
return x_9;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_9, 0);
x_525 = lean_ctor_get(x_9, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_9);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___redArg(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Meta_Canonicalizer_canon_spec__0(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_Canonicalizer_canon_spec__4(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_List_forIn_x27_loop___at___Lean_Meta_Canonicalizer_canon_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_4);
return x_16;
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
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_FunInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Canonicalizer(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__0 = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__0();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__0);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1 = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__1);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__2 = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__2();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited___closed__2);
l_Lean_Meta_Canonicalizer_instInhabitedExprVisited = _init_l_Lean_Meta_Canonicalizer_instInhabitedExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedExprVisited);
l_Lean_Meta_Canonicalizer_instBEqExprVisited = _init_l_Lean_Meta_Canonicalizer_instBEqExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instBEqExprVisited);
l_Lean_Meta_Canonicalizer_instHashableExprVisited = _init_l_Lean_Meta_Canonicalizer_instHashableExprVisited();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instHashableExprVisited);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__0);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__1);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__2);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__3);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__4);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__5 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__5();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__5);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__6 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__6();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__6);
l_Lean_Meta_Canonicalizer_instInhabitedState___closed__7 = _init_l_Lean_Meta_Canonicalizer_instInhabitedState___closed__7();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState___closed__7);
l_Lean_Meta_Canonicalizer_instInhabitedState = _init_l_Lean_Meta_Canonicalizer_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_instInhabitedState);
l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0 = _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__0);
l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1 = _init_l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Canonicalizer_0__Lean_Meta_Canonicalizer_mkKey___closed__1);
l_Lean_Meta_Canonicalizer_canon___closed__0 = _init_l_Lean_Meta_Canonicalizer_canon___closed__0();
lean_mark_persistent(l_Lean_Meta_Canonicalizer_canon___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
