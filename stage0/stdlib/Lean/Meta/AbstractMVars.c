// Lean compiler output
// Module: Lean.Meta.AbstractMVars
// Imports: Init Lean.Meta.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_StateT_get___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult;
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3;
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1;
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqAbstractMVarsResult___closed__1;
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_abstractMVars___closed__1;
uint64_t l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_500_(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1890_(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_emap___default;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1___boxed(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_nextParamIdx___default;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1(lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_lmap___default;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_375_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAbstractMVarsResult;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_paramNames___default;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_fvars___default;
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__6(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAbstractMVarsResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_array_get_size(x_3);
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1(x_3, x_6, lean_box(0), x_3, x_6, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_4, x_7);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_expr_eqv(x_5, x_8);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instBEqAbstractMVarsResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instBEqAbstractMVarsResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instBEqAbstractMVarsResult___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_nextParamIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_paramNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_fvars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_lmap___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_emap___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateT_get___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 2, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_ctor_get(x_2, 5);
x_14 = lean_ctor_get(x_2, 6);
x_15 = lean_ctor_get(x_2, 7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_16 = lean_apply_1(x_1, x_10);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_11);
lean_ctor_set(x_17, 4, x_12);
lean_ctor_set(x_17, 5, x_13);
lean_ctor_set(x_17, 6, x_14);
lean_ctor_set(x_17, 7, x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateT_get___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__2), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1;
x_2 = l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2;
x_3 = lean_alloc_closure((void*)(l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = l_Lean_Name_num___override(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Lean_Name_num___override(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
x_24 = lean_ctor_get(x_1, 6);
x_25 = lean_ctor_get(x_1, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_28 = x_18;
} else {
 lean_dec_ref(x_18);
 x_28 = lean_box(0);
}
lean_inc(x_27);
lean_inc(x_26);
x_29 = l_Lean_Name_num___override(x_26, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_27, x_30);
lean_dec(x_27);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_20);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set(x_33, 4, x_22);
lean_ctor_set(x_33, 5, x_23);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_AbstractMVars_mkFreshId(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_500_(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_500_(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_500_(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_500_(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__5(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l___private_Lean_Level_0__Lean_hashLevelMVarId____x40_Lean_Level___hyg_500_(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__5(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_abstMVar", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Level_hasMVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_10 = lean_ptr_addr(x_8);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Level_succ___override(x_8);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Level_succ___override(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
x_23 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_21, x_2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_22, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_30 = lean_ptr_addr(x_24);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
lean_dec(x_1);
x_32 = l_Lean_mkLevelMax_x27(x_24, x_28);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_34 = lean_ptr_addr(x_28);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_Lean_mkLevelMax_x27(x_24, x_28);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_simpLevelMax_x27(x_24, x_28, x_1);
lean_dec(x_1);
lean_dec(x_28);
lean_dec(x_24);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_ptr_addr(x_21);
lean_dec(x_21);
x_41 = lean_ptr_addr(x_24);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_22);
lean_dec(x_1);
x_43 = l_Lean_mkLevelMax_x27(x_24, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = lean_ptr_addr(x_22);
lean_dec(x_22);
x_46 = lean_ptr_addr(x_38);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = l_Lean_mkLevelMax_x27(x_24, x_38);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_simpLevelMax_x27(x_24, x_38, x_1);
lean_dec(x_1);
lean_dec(x_38);
lean_dec(x_24);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
return x_51;
}
}
}
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
x_54 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_52, x_2);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_53);
x_57 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_53, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; size_t x_60; size_t x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_61 = lean_ptr_addr(x_55);
x_62 = lean_usize_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_53);
lean_dec(x_1);
x_63 = l_Lean_mkLevelIMax_x27(x_55, x_59);
lean_ctor_set(x_57, 0, x_63);
return x_57;
}
else
{
size_t x_64; size_t x_65; uint8_t x_66; 
x_64 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_65 = lean_ptr_addr(x_59);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_1);
x_67 = l_Lean_mkLevelIMax_x27(x_55, x_59);
lean_ctor_set(x_57, 0, x_67);
return x_57;
}
else
{
lean_object* x_68; 
x_68 = l_Lean_simpLevelIMax_x27(x_55, x_59, x_1);
lean_dec(x_1);
lean_ctor_set(x_57, 0, x_68);
return x_57;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
x_71 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_72 = lean_ptr_addr(x_55);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
lean_dec(x_1);
x_74 = l_Lean_mkLevelIMax_x27(x_55, x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_77 = lean_ptr_addr(x_69);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_79 = l_Lean_mkLevelIMax_x27(x_55, x_69);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_simpLevelIMax_x27(x_55, x_69, x_1);
lean_dec(x_1);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_70);
return x_82;
}
}
}
}
case 5:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 2);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_84);
x_85 = l_Lean_MetavarContext_getLevelDepth(x_84, x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_nat_dec_eq(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_84);
lean_dec(x_83);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_2);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_2, 6);
lean_inc(x_89);
lean_inc(x_83);
lean_inc(x_89);
x_90 = l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(x_89, x_83);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_91 = lean_ctor_get(x_2, 3);
lean_inc(x_91);
x_92 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_inc(x_91);
x_93 = l_Lean_Name_num___override(x_92, x_91);
lean_inc(x_93);
x_94 = l_Lean_Level_param___override(x_93);
x_95 = lean_ctor_get(x_2, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_91, x_97);
lean_dec(x_91);
x_99 = lean_ctor_get(x_2, 4);
lean_inc(x_99);
x_100 = lean_array_push(x_99, x_93);
x_101 = lean_ctor_get(x_2, 5);
lean_inc(x_101);
lean_inc(x_94);
x_102 = l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_89, x_83, x_94);
x_103 = lean_ctor_get(x_2, 7);
lean_inc(x_103);
lean_dec(x_2);
x_104 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_84);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_100);
lean_ctor_set(x_104, 5, x_101);
lean_ctor_set(x_104, 6, x_102);
lean_ctor_set(x_104, 7, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_89);
lean_dec(x_84);
lean_dec(x_83);
x_106 = lean_ctor_get(x_90, 0);
lean_inc(x_106);
lean_dec(x_90);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_2);
return x_107;
}
}
}
default: 
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_2);
return x_108;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_instantiateMVarsCore(x_6, x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_2, 2, x_9);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
x_18 = lean_ctor_get(x_2, 5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_ctor_get(x_2, 7);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_21 = l_Lean_instantiateMVarsCore(x_15, x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_16);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_18);
lean_ctor_set(x_25, 6, x_19);
lean_ctor_set(x_25, 7, x_20);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1890_(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1890_(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1890_(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__8(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__7(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1890_(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__6(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1890_(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Lean_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__6(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_7, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_11;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_14;
x_2 = x_18;
x_3 = x_17;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_6);
x_7 = l_Lean_MetavarContext_getDecl(x_6, x_5);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_12 = l_Lean_instantiateMVars___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(x_1, x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_expr_eqv(x_1, x_14);
lean_dec(x_1);
if (x_16 == 0)
{
lean_free_object(x_12);
lean_dec(x_7);
lean_dec(x_5);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 7);
lean_inc(x_18);
lean_inc(x_5);
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_18, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_12);
x_20 = lean_ctor_get(x_7, 2);
lean_inc(x_20);
x_21 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_20, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_28 = l_Lean_Expr_fvar___override(x_26);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec(x_7);
x_30 = l_Lean_Name_isAnonymous(x_29);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 5);
lean_inc(x_36);
lean_inc(x_28);
lean_inc(x_36);
x_37 = lean_array_push(x_36, x_28);
x_38 = lean_ctor_get(x_27, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_27, 7);
lean_inc(x_39);
lean_dec(x_27);
lean_inc(x_28);
x_40 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_39, x_5, x_28);
if (x_30 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
x_41 = 0;
x_42 = lean_local_ctx_mk_local_decl(x_32, x_26, x_29, x_22, x_41);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_37);
lean_ctor_set(x_43, 6, x_38);
lean_ctor_set(x_43, 7, x_40);
lean_ctor_set(x_24, 1, x_43);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_29);
x_44 = lean_array_get_size(x_36);
lean_dec(x_36);
x_45 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_46 = lean_name_append_index_after(x_45, x_44);
x_47 = 0;
x_48 = lean_local_ctx_mk_local_decl(x_32, x_26, x_46, x_22, x_47);
x_49 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_33);
lean_ctor_set(x_49, 3, x_34);
lean_ctor_set(x_49, 4, x_35);
lean_ctor_set(x_49, 5, x_37);
lean_ctor_set(x_49, 6, x_38);
lean_ctor_set(x_49, 7, x_40);
lean_ctor_set(x_24, 1, x_49);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
lean_inc(x_50);
x_52 = l_Lean_Expr_fvar___override(x_50);
x_53 = lean_ctor_get(x_7, 0);
lean_inc(x_53);
lean_dec(x_7);
x_54 = l_Lean_Name_isAnonymous(x_53);
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 5);
lean_inc(x_60);
lean_inc(x_52);
lean_inc(x_60);
x_61 = lean_array_push(x_60, x_52);
x_62 = lean_ctor_get(x_51, 6);
lean_inc(x_62);
x_63 = lean_ctor_get(x_51, 7);
lean_inc(x_63);
lean_dec(x_51);
lean_inc(x_52);
x_64 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_63, x_5, x_52);
if (x_54 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
x_65 = 0;
x_66 = lean_local_ctx_mk_local_decl(x_56, x_50, x_53, x_22, x_65);
x_67 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_57);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_61);
lean_ctor_set(x_67, 6, x_62);
lean_ctor_set(x_67, 7, x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
x_69 = lean_array_get_size(x_60);
lean_dec(x_60);
x_70 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_71 = lean_name_append_index_after(x_70, x_69);
x_72 = 0;
x_73 = lean_local_ctx_mk_local_decl(x_56, x_50, x_71, x_22, x_72);
x_74 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_74, 0, x_55);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_57);
lean_ctor_set(x_74, 3, x_58);
lean_ctor_set(x_74, 4, x_59);
lean_ctor_set(x_74, 5, x_61);
lean_ctor_set(x_74, 6, x_62);
lean_ctor_set(x_74, 7, x_64);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_52);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_7);
lean_dec(x_5);
x_76 = lean_ctor_get(x_19, 0);
lean_inc(x_76);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_76);
return x_12;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_12);
x_79 = lean_expr_eqv(x_1, x_77);
lean_dec(x_1);
if (x_79 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
x_1 = x_77;
x_2 = x_78;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_77);
x_81 = lean_ctor_get(x_78, 7);
lean_inc(x_81);
lean_inc(x_5);
x_82 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_81, x_5);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_83 = lean_ctor_get(x_7, 2);
lean_inc(x_83);
x_84 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_83, x_78);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
lean_inc(x_88);
x_91 = l_Lean_Expr_fvar___override(x_88);
x_92 = lean_ctor_get(x_7, 0);
lean_inc(x_92);
lean_dec(x_7);
x_93 = l_Lean_Name_isAnonymous(x_92);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_89, 4);
lean_inc(x_98);
x_99 = lean_ctor_get(x_89, 5);
lean_inc(x_99);
lean_inc(x_91);
lean_inc(x_99);
x_100 = lean_array_push(x_99, x_91);
x_101 = lean_ctor_get(x_89, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_89, 7);
lean_inc(x_102);
lean_dec(x_89);
lean_inc(x_91);
x_103 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_102, x_5, x_91);
if (x_93 == 0)
{
uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_99);
x_104 = 0;
x_105 = lean_local_ctx_mk_local_decl(x_95, x_88, x_92, x_85, x_104);
x_106 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_96);
lean_ctor_set(x_106, 3, x_97);
lean_ctor_set(x_106, 4, x_98);
lean_ctor_set(x_106, 5, x_100);
lean_ctor_set(x_106, 6, x_101);
lean_ctor_set(x_106, 7, x_103);
if (lean_is_scalar(x_90)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_90;
}
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_92);
x_108 = lean_array_get_size(x_99);
lean_dec(x_99);
x_109 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_110 = lean_name_append_index_after(x_109, x_108);
x_111 = 0;
x_112 = lean_local_ctx_mk_local_decl(x_95, x_88, x_110, x_85, x_111);
x_113 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_113, 0, x_94);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_96);
lean_ctor_set(x_113, 3, x_97);
lean_ctor_set(x_113, 4, x_98);
lean_ctor_set(x_113, 5, x_100);
lean_ctor_set(x_113, 6, x_101);
lean_ctor_set(x_113, 7, x_103);
if (lean_is_scalar(x_90)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_90;
}
lean_ctor_set(x_114, 0, x_91);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_7);
lean_dec(x_5);
x_115 = lean_ctor_get(x_82, 0);
lean_inc(x_115);
lean_dec(x_82);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_78);
return x_116;
}
}
}
}
}
case 3:
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
lean_inc(x_117);
x_118 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_117, x_2);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; size_t x_121; size_t x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ptr_addr(x_117);
lean_dec(x_117);
x_122 = lean_ptr_addr(x_120);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_1);
x_124 = l_Lean_Expr_sort___override(x_120);
lean_ctor_set(x_118, 0, x_124);
return x_118;
}
else
{
lean_dec(x_120);
lean_ctor_set(x_118, 0, x_1);
return x_118;
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_118, 0);
x_126 = lean_ctor_get(x_118, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_118);
x_127 = lean_ptr_addr(x_117);
lean_dec(x_117);
x_128 = lean_ptr_addr(x_125);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_1);
x_130 = l_Lean_Expr_sort___override(x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec(x_125);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_126);
return x_132;
}
}
}
case 4:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 1);
lean_inc(x_134);
x_135 = lean_box(0);
lean_inc(x_134);
x_136 = l_List_mapM_loop___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(x_134, x_135, x_2);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = l_ptrEqList___rarg(x_134, x_138);
lean_dec(x_134);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_1);
x_140 = l_Lean_Expr_const___override(x_133, x_138);
lean_ctor_set(x_136, 0, x_140);
return x_136;
}
else
{
lean_dec(x_138);
lean_dec(x_133);
lean_ctor_set(x_136, 0, x_1);
return x_136;
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_136, 0);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_136);
x_143 = l_ptrEqList___rarg(x_134, x_141);
lean_dec(x_134);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_1);
x_144 = l_Lean_Expr_const___override(x_133, x_141);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; 
lean_dec(x_141);
lean_dec(x_133);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_142);
return x_146;
}
}
}
case 5:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_147 = lean_ctor_get(x_1, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 1);
lean_inc(x_148);
lean_inc(x_147);
x_149 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_147, x_2);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_148);
x_152 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_148, x_151);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; size_t x_155; size_t x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ptr_addr(x_147);
lean_dec(x_147);
x_156 = lean_ptr_addr(x_150);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec(x_148);
lean_dec(x_1);
x_158 = l_Lean_Expr_app___override(x_150, x_154);
lean_ctor_set(x_152, 0, x_158);
return x_152;
}
else
{
size_t x_159; size_t x_160; uint8_t x_161; 
x_159 = lean_ptr_addr(x_148);
lean_dec(x_148);
x_160 = lean_ptr_addr(x_154);
x_161 = lean_usize_dec_eq(x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_1);
x_162 = l_Lean_Expr_app___override(x_150, x_154);
lean_ctor_set(x_152, 0, x_162);
return x_152;
}
else
{
lean_dec(x_154);
lean_dec(x_150);
lean_ctor_set(x_152, 0, x_1);
return x_152;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; size_t x_165; size_t x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_152, 0);
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_152);
x_165 = lean_ptr_addr(x_147);
lean_dec(x_147);
x_166 = lean_ptr_addr(x_150);
x_167 = lean_usize_dec_eq(x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_148);
lean_dec(x_1);
x_168 = l_Lean_Expr_app___override(x_150, x_163);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
return x_169;
}
else
{
size_t x_170; size_t x_171; uint8_t x_172; 
x_170 = lean_ptr_addr(x_148);
lean_dec(x_148);
x_171 = lean_ptr_addr(x_163);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_173 = l_Lean_Expr_app___override(x_150, x_163);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_164);
return x_174;
}
else
{
lean_object* x_175; 
lean_dec(x_163);
lean_dec(x_150);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_1);
lean_ctor_set(x_175, 1, x_164);
return x_175;
}
}
}
}
case 6:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_1, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_1, 2);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_177);
x_180 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_177, x_2);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_178);
x_183 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_178, x_182);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; size_t x_187; size_t x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
x_186 = l_Lean_Expr_lam___override(x_176, x_177, x_178, x_179);
x_187 = lean_ptr_addr(x_177);
lean_dec(x_177);
x_188 = lean_ptr_addr(x_181);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_186);
lean_dec(x_178);
x_190 = l_Lean_Expr_lam___override(x_176, x_181, x_185, x_179);
lean_ctor_set(x_183, 0, x_190);
return x_183;
}
else
{
size_t x_191; size_t x_192; uint8_t x_193; 
x_191 = lean_ptr_addr(x_178);
lean_dec(x_178);
x_192 = lean_ptr_addr(x_185);
x_193 = lean_usize_dec_eq(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_186);
x_194 = l_Lean_Expr_lam___override(x_176, x_181, x_185, x_179);
lean_ctor_set(x_183, 0, x_194);
return x_183;
}
else
{
uint8_t x_195; 
x_195 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_375_(x_179, x_179);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_186);
x_196 = l_Lean_Expr_lam___override(x_176, x_181, x_185, x_179);
lean_ctor_set(x_183, 0, x_196);
return x_183;
}
else
{
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_176);
lean_ctor_set(x_183, 0, x_186);
return x_183;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; size_t x_201; uint8_t x_202; 
x_197 = lean_ctor_get(x_183, 0);
x_198 = lean_ctor_get(x_183, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_183);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
x_199 = l_Lean_Expr_lam___override(x_176, x_177, x_178, x_179);
x_200 = lean_ptr_addr(x_177);
lean_dec(x_177);
x_201 = lean_ptr_addr(x_181);
x_202 = lean_usize_dec_eq(x_200, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_199);
lean_dec(x_178);
x_203 = l_Lean_Expr_lam___override(x_176, x_181, x_197, x_179);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_198);
return x_204;
}
else
{
size_t x_205; size_t x_206; uint8_t x_207; 
x_205 = lean_ptr_addr(x_178);
lean_dec(x_178);
x_206 = lean_ptr_addr(x_197);
x_207 = lean_usize_dec_eq(x_205, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_199);
x_208 = l_Lean_Expr_lam___override(x_176, x_181, x_197, x_179);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_198);
return x_209;
}
else
{
uint8_t x_210; 
x_210 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_375_(x_179, x_179);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_199);
x_211 = l_Lean_Expr_lam___override(x_176, x_181, x_197, x_179);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_198);
return x_212;
}
else
{
lean_object* x_213; 
lean_dec(x_197);
lean_dec(x_181);
lean_dec(x_176);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_199);
lean_ctor_set(x_213, 1, x_198);
return x_213;
}
}
}
}
}
case 7:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_214 = lean_ctor_get(x_1, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_1, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_1, 2);
lean_inc(x_216);
x_217 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_215);
x_218 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_215, x_2);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
lean_inc(x_216);
x_221 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_216, x_220);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_224 = l_Lean_Expr_forallE___override(x_214, x_215, x_216, x_217);
x_225 = lean_ptr_addr(x_215);
lean_dec(x_215);
x_226 = lean_ptr_addr(x_219);
x_227 = lean_usize_dec_eq(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_224);
lean_dec(x_216);
x_228 = l_Lean_Expr_forallE___override(x_214, x_219, x_223, x_217);
lean_ctor_set(x_221, 0, x_228);
return x_221;
}
else
{
size_t x_229; size_t x_230; uint8_t x_231; 
x_229 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_230 = lean_ptr_addr(x_223);
x_231 = lean_usize_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_224);
x_232 = l_Lean_Expr_forallE___override(x_214, x_219, x_223, x_217);
lean_ctor_set(x_221, 0, x_232);
return x_221;
}
else
{
uint8_t x_233; 
x_233 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_375_(x_217, x_217);
if (x_233 == 0)
{
lean_object* x_234; 
lean_dec(x_224);
x_234 = l_Lean_Expr_forallE___override(x_214, x_219, x_223, x_217);
lean_ctor_set(x_221, 0, x_234);
return x_221;
}
else
{
lean_dec(x_223);
lean_dec(x_219);
lean_dec(x_214);
lean_ctor_set(x_221, 0, x_224);
return x_221;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; size_t x_238; size_t x_239; uint8_t x_240; 
x_235 = lean_ctor_get(x_221, 0);
x_236 = lean_ctor_get(x_221, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_221);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_237 = l_Lean_Expr_forallE___override(x_214, x_215, x_216, x_217);
x_238 = lean_ptr_addr(x_215);
lean_dec(x_215);
x_239 = lean_ptr_addr(x_219);
x_240 = lean_usize_dec_eq(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_237);
lean_dec(x_216);
x_241 = l_Lean_Expr_forallE___override(x_214, x_219, x_235, x_217);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_236);
return x_242;
}
else
{
size_t x_243; size_t x_244; uint8_t x_245; 
x_243 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_244 = lean_ptr_addr(x_235);
x_245 = lean_usize_dec_eq(x_243, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_237);
x_246 = l_Lean_Expr_forallE___override(x_214, x_219, x_235, x_217);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_236);
return x_247;
}
else
{
uint8_t x_248; 
x_248 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_375_(x_217, x_217);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_237);
x_249 = l_Lean_Expr_forallE___override(x_214, x_219, x_235, x_217);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_236);
return x_250;
}
else
{
lean_object* x_251; 
lean_dec(x_235);
lean_dec(x_219);
lean_dec(x_214);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_237);
lean_ctor_set(x_251, 1, x_236);
return x_251;
}
}
}
}
}
case 8:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_252 = lean_ctor_get(x_1, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_1, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_1, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_1, 3);
lean_inc(x_255);
x_256 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_inc(x_253);
x_257 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_253, x_2);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
lean_inc(x_254);
x_260 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_254, x_259);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_255);
x_263 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_255, x_262);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; size_t x_266; size_t x_267; uint8_t x_268; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_ptr_addr(x_253);
lean_dec(x_253);
x_267 = lean_ptr_addr(x_258);
x_268 = lean_usize_dec_eq(x_266, x_267);
if (x_268 == 0)
{
lean_object* x_269; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_1);
x_269 = l_Lean_Expr_letE___override(x_252, x_258, x_261, x_265, x_256);
lean_ctor_set(x_263, 0, x_269);
return x_263;
}
else
{
size_t x_270; size_t x_271; uint8_t x_272; 
x_270 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_271 = lean_ptr_addr(x_261);
x_272 = lean_usize_dec_eq(x_270, x_271);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec(x_255);
lean_dec(x_1);
x_273 = l_Lean_Expr_letE___override(x_252, x_258, x_261, x_265, x_256);
lean_ctor_set(x_263, 0, x_273);
return x_263;
}
else
{
size_t x_274; size_t x_275; uint8_t x_276; 
x_274 = lean_ptr_addr(x_255);
lean_dec(x_255);
x_275 = lean_ptr_addr(x_265);
x_276 = lean_usize_dec_eq(x_274, x_275);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_1);
x_277 = l_Lean_Expr_letE___override(x_252, x_258, x_261, x_265, x_256);
lean_ctor_set(x_263, 0, x_277);
return x_263;
}
else
{
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_252);
lean_ctor_set(x_263, 0, x_1);
return x_263;
}
}
}
}
else
{
lean_object* x_278; lean_object* x_279; size_t x_280; size_t x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_263, 0);
x_279 = lean_ctor_get(x_263, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_263);
x_280 = lean_ptr_addr(x_253);
lean_dec(x_253);
x_281 = lean_ptr_addr(x_258);
x_282 = lean_usize_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_1);
x_283 = l_Lean_Expr_letE___override(x_252, x_258, x_261, x_278, x_256);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_279);
return x_284;
}
else
{
size_t x_285; size_t x_286; uint8_t x_287; 
x_285 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_286 = lean_ptr_addr(x_261);
x_287 = lean_usize_dec_eq(x_285, x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_255);
lean_dec(x_1);
x_288 = l_Lean_Expr_letE___override(x_252, x_258, x_261, x_278, x_256);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_279);
return x_289;
}
else
{
size_t x_290; size_t x_291; uint8_t x_292; 
x_290 = lean_ptr_addr(x_255);
lean_dec(x_255);
x_291 = lean_ptr_addr(x_278);
x_292 = lean_usize_dec_eq(x_290, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_1);
x_293 = l_Lean_Expr_letE___override(x_252, x_258, x_261, x_278, x_256);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_279);
return x_294;
}
else
{
lean_object* x_295; 
lean_dec(x_278);
lean_dec(x_261);
lean_dec(x_258);
lean_dec(x_252);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_1);
lean_ctor_set(x_295, 1, x_279);
return x_295;
}
}
}
}
}
case 10:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_ctor_get(x_1, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_1, 1);
lean_inc(x_297);
lean_inc(x_297);
x_298 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_297, x_2);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; size_t x_301; size_t x_302; uint8_t x_303; 
x_300 = lean_ctor_get(x_298, 0);
x_301 = lean_ptr_addr(x_297);
lean_dec(x_297);
x_302 = lean_ptr_addr(x_300);
x_303 = lean_usize_dec_eq(x_301, x_302);
if (x_303 == 0)
{
lean_object* x_304; 
lean_dec(x_1);
x_304 = l_Lean_Expr_mdata___override(x_296, x_300);
lean_ctor_set(x_298, 0, x_304);
return x_298;
}
else
{
lean_dec(x_300);
lean_dec(x_296);
lean_ctor_set(x_298, 0, x_1);
return x_298;
}
}
else
{
lean_object* x_305; lean_object* x_306; size_t x_307; size_t x_308; uint8_t x_309; 
x_305 = lean_ctor_get(x_298, 0);
x_306 = lean_ctor_get(x_298, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_298);
x_307 = lean_ptr_addr(x_297);
lean_dec(x_297);
x_308 = lean_ptr_addr(x_305);
x_309 = lean_usize_dec_eq(x_307, x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_1);
x_310 = l_Lean_Expr_mdata___override(x_296, x_305);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_306);
return x_311;
}
else
{
lean_object* x_312; 
lean_dec(x_305);
lean_dec(x_296);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_1);
lean_ctor_set(x_312, 1, x_306);
return x_312;
}
}
}
case 11:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_313 = lean_ctor_get(x_1, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_1, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_1, 2);
lean_inc(x_315);
lean_inc(x_315);
x_316 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_315, x_2);
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
lean_object* x_318; size_t x_319; size_t x_320; uint8_t x_321; 
x_318 = lean_ctor_get(x_316, 0);
x_319 = lean_ptr_addr(x_315);
lean_dec(x_315);
x_320 = lean_ptr_addr(x_318);
x_321 = lean_usize_dec_eq(x_319, x_320);
if (x_321 == 0)
{
lean_object* x_322; 
lean_dec(x_1);
x_322 = l_Lean_Expr_proj___override(x_313, x_314, x_318);
lean_ctor_set(x_316, 0, x_322);
return x_316;
}
else
{
lean_dec(x_318);
lean_dec(x_314);
lean_dec(x_313);
lean_ctor_set(x_316, 0, x_1);
return x_316;
}
}
else
{
lean_object* x_323; lean_object* x_324; size_t x_325; size_t x_326; uint8_t x_327; 
x_323 = lean_ctor_get(x_316, 0);
x_324 = lean_ctor_get(x_316, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_316);
x_325 = lean_ptr_addr(x_315);
lean_dec(x_315);
x_326 = lean_ptr_addr(x_323);
x_327 = lean_usize_dec_eq(x_325, x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_1);
x_328 = l_Lean_Expr_proj___override(x_313, x_314, x_323);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_324);
return x_329;
}
else
{
lean_object* x_330; 
lean_dec(x_323);
lean_dec(x_314);
lean_dec(x_313);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_1);
lean_ctor_set(x_330, 1, x_324);
return x_330;
}
}
}
default: 
{
lean_object* x_331; 
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_1);
lean_ctor_set(x_331, 1, x_2);
return x_331;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_abstractMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_7 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_st_ref_get(x_5, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
x_23 = l_Lean_Meta_abstractMVars___closed__1;
lean_inc(x_16);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set(x_24, 7, x_23);
x_25 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_st_ref_take(x_5, x_19);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_30, 2);
lean_dec(x_33);
lean_ctor_set(x_30, 2, x_28);
x_34 = lean_st_ref_set(x_5, x_30, x_31);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_27, 2);
lean_inc(x_36);
x_37 = lean_st_ref_get(x_5, x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_3, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
lean_ctor_set(x_40, 0, x_36);
x_44 = lean_st_ref_set(x_3, x_40, x_41);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_27, 5);
lean_inc(x_48);
x_49 = l_Lean_LocalContext_mkLambda(x_47, x_48, x_26);
x_50 = lean_ctor_get(x_27, 4);
lean_inc(x_50);
lean_dec(x_27);
x_51 = lean_array_get_size(x_48);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec(x_44);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_27, 5);
lean_inc(x_55);
x_56 = l_Lean_LocalContext_mkLambda(x_54, x_55, x_26);
x_57 = lean_ctor_get(x_27, 4);
lean_inc(x_57);
lean_dec(x_27);
x_58 = lean_array_get_size(x_55);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = lean_ctor_get(x_40, 1);
x_62 = lean_ctor_get(x_40, 2);
x_63 = lean_ctor_get(x_40, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_40);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_36);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_st_ref_set(x_3, x_64, x_41);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_27, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_27, 5);
lean_inc(x_69);
x_70 = l_Lean_LocalContext_mkLambda(x_68, x_69, x_26);
x_71 = lean_ctor_get(x_27, 4);
lean_inc(x_71);
lean_dec(x_27);
x_72 = lean_array_get_size(x_69);
lean_dec(x_69);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
if (lean_is_scalar(x_67)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_67;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_75 = lean_ctor_get(x_30, 0);
x_76 = lean_ctor_get(x_30, 1);
x_77 = lean_ctor_get(x_30, 3);
x_78 = lean_ctor_get(x_30, 4);
x_79 = lean_ctor_get(x_30, 5);
x_80 = lean_ctor_get(x_30, 6);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_30);
x_81 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_79);
lean_ctor_set(x_81, 6, x_80);
x_82 = lean_st_ref_set(x_5, x_81, x_31);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_27, 2);
lean_inc(x_84);
x_85 = lean_st_ref_get(x_5, x_83);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_st_ref_take(x_3, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 4, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_84);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_91);
lean_ctor_set(x_94, 3, x_92);
x_95 = lean_st_ref_set(x_3, x_94, x_89);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_27, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_27, 5);
lean_inc(x_99);
x_100 = l_Lean_LocalContext_mkLambda(x_98, x_99, x_26);
x_101 = lean_ctor_get(x_27, 4);
lean_inc(x_101);
lean_dec(x_27);
x_102 = lean_array_get_size(x_99);
lean_dec(x_99);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_100);
if (lean_is_scalar(x_97)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_97;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
return x_104;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_abstractMVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_12, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_8 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
lean_inc(x_7);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(x_9, x_10, x_7, x_2, x_3, x_4, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_7, x_12, x_14);
lean_dec(x_12);
lean_dec(x_7);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_lambdaMetaTelescope(x_15, x_17, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_17);
lean_dec(x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_openAbstractMVarsResult(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AbstractMVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1 = _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1);
l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2 = _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2);
l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3 = _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3);
l_Lean_Meta_instInhabitedAbstractMVarsResult = _init_l_Lean_Meta_instInhabitedAbstractMVarsResult();
lean_mark_persistent(l_Lean_Meta_instInhabitedAbstractMVarsResult);
l_Lean_Meta_instBEqAbstractMVarsResult___closed__1 = _init_l_Lean_Meta_instBEqAbstractMVarsResult___closed__1();
lean_mark_persistent(l_Lean_Meta_instBEqAbstractMVarsResult___closed__1);
l_Lean_Meta_instBEqAbstractMVarsResult = _init_l_Lean_Meta_instBEqAbstractMVarsResult();
lean_mark_persistent(l_Lean_Meta_instBEqAbstractMVarsResult);
l_Lean_Meta_AbstractMVars_State_nextParamIdx___default = _init_l_Lean_Meta_AbstractMVars_State_nextParamIdx___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_nextParamIdx___default);
l_Lean_Meta_AbstractMVars_State_paramNames___default = _init_l_Lean_Meta_AbstractMVars_State_paramNames___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_paramNames___default);
l_Lean_Meta_AbstractMVars_State_fvars___default = _init_l_Lean_Meta_AbstractMVars_State_fvars___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_fvars___default);
l_Lean_Meta_AbstractMVars_State_lmap___default = _init_l_Lean_Meta_AbstractMVars_State_lmap___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_lmap___default);
l_Lean_Meta_AbstractMVars_State_emap___default = _init_l_Lean_Meta_AbstractMVars_State_emap___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_emap___default);
l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1 = _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1);
l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2 = _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2);
l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3 = _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3);
l_Lean_Meta_AbstractMVars_instMonadMCtxM = _init_l_Lean_Meta_AbstractMVars_instMonadMCtxM();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_instMonadMCtxM);
l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1 = _init_l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1);
l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2 = _init_l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2);
l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1 = _init_l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1);
l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2 = _init_l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2);
l_Lean_Meta_abstractMVars___closed__1 = _init_l_Lean_Meta_abstractMVars___closed__1();
lean_mark_persistent(l_Lean_Meta_abstractMVars___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
