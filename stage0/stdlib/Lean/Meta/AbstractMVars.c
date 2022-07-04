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
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__8(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_StateT_get___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult;
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__3;
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(lean_object*, lean_object*);
static uint64_t l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__1;
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqAbstractMVarsResult___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_abstractMVars___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_emap___default;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_instMonadMCtxM___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1___boxed(lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_nextParamIdx___default;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
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
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_42____boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAbstractMVarsResult;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_paramNames___default;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_fvars___default;
LEAN_EXPORT lean_object* l_StateT_bind___at_Lean_Meta_AbstractMVars_instMonadMCtxM___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
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
static uint64_t _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3;
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
x_1 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4;
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
x_7 = lean_name_mk_numeral(x_5, x_6);
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
x_13 = lean_name_mk_numeral(x_11, x_12);
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
x_29 = lean_name_mk_numeral(x_26, x_27);
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
x_5 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_2);
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
x_7 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_4);
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
x_17 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_13);
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
x_8 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_2);
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
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
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
x_25 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_2);
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
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
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
x_3 = lean_name_mk_string(x_1, x_2);
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_6, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_level_update_succ(x_1, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_level_update_succ(x_1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_15);
x_17 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_15, x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set_uint64(x_21, sizeof(void*)*1, x_16);
x_22 = lean_level_update_succ(x_21, x_18);
if (lean_is_scalar(x_20)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_20;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
case 2:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_27 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_25, x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_26);
x_30 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_26, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_level_update_max(x_1, x_28, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_level_update_max(x_1, x_28, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
lean_inc(x_38);
x_41 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_38, x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_39);
x_44 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_39, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set_uint64(x_48, sizeof(void*)*2, x_40);
x_49 = lean_level_update_max(x_48, x_42, x_45);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
case 3:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
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
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_level_update_imax(x_1, x_55, x_59);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_level_update_imax(x_1, x_55, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_1, 0);
x_66 = lean_ctor_get(x_1, 1);
x_67 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_1);
lean_inc(x_65);
x_68 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_65, x_2);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_66);
x_71 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_66, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set_uint64(x_75, sizeof(void*)*2, x_67);
x_76 = lean_level_update_imax(x_75, x_69, x_72);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
case 5:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 7);
lean_inc(x_86);
lean_inc(x_78);
lean_inc(x_81);
x_87 = l_Lean_MetavarContext_getLevelDepth(x_81, x_78);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_2);
return x_90;
}
else
{
lean_object* x_91; 
lean_dec(x_1);
lean_inc(x_78);
lean_inc(x_85);
x_91 = l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(x_85, x_78);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_93 = lean_ctor_get(x_2, 7);
lean_dec(x_93);
x_94 = lean_ctor_get(x_2, 6);
lean_dec(x_94);
x_95 = lean_ctor_get(x_2, 5);
lean_dec(x_95);
x_96 = lean_ctor_get(x_2, 4);
lean_dec(x_96);
x_97 = lean_ctor_get(x_2, 3);
lean_dec(x_97);
x_98 = lean_ctor_get(x_2, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_2, 0);
lean_dec(x_100);
x_101 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_inc(x_82);
x_102 = lean_name_mk_numeral(x_101, x_82);
lean_inc(x_102);
x_103 = l_Lean_mkLevelParam(x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_82, x_104);
lean_dec(x_82);
x_106 = lean_array_push(x_83, x_102);
lean_inc(x_103);
x_107 = l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_85, x_78, x_103);
lean_ctor_set(x_2, 6, x_107);
lean_ctor_set(x_2, 4, x_106);
lean_ctor_set(x_2, 3, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_2);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_2);
x_109 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_inc(x_82);
x_110 = lean_name_mk_numeral(x_109, x_82);
lean_inc(x_110);
x_111 = l_Lean_mkLevelParam(x_110);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_82, x_112);
lean_dec(x_82);
x_114 = lean_array_push(x_83, x_110);
lean_inc(x_111);
x_115 = l_Std_HashMap_insert___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__3(x_85, x_78, x_111);
x_116 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_116, 0, x_79);
lean_ctor_set(x_116, 1, x_80);
lean_ctor_set(x_116, 2, x_81);
lean_ctor_set(x_116, 3, x_113);
lean_ctor_set(x_116, 4, x_114);
lean_ctor_set(x_116, 5, x_84);
lean_ctor_set(x_116, 6, x_115);
lean_ctor_set(x_116, 7, x_86);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
x_118 = lean_ctor_get(x_91, 0);
lean_inc(x_118);
lean_dec(x_91);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_2);
return x_119;
}
}
}
default: 
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_2);
return x_120;
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
x_5 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_2);
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
x_7 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_4);
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
x_17 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_13);
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
x_8 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_2);
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
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
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
x_25 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_475_(x_2);
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
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
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
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_6, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_9);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_17, x_2);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
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
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_28 = l_Lean_mkFVar(x_26);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec(x_7);
x_30 = l_Lean_Name_isAnonymous(x_29);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 1);
x_33 = lean_ctor_get(x_27, 5);
x_34 = lean_ctor_get(x_27, 7);
lean_inc(x_28);
lean_inc(x_33);
x_35 = lean_array_push(x_33, x_28);
lean_inc(x_28);
x_36 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_34, x_5, x_28);
if (x_30 == 0)
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_33);
x_37 = 0;
x_38 = lean_local_ctx_mk_local_decl(x_32, x_26, x_29, x_22, x_37);
lean_ctor_set(x_27, 7, x_36);
lean_ctor_set(x_27, 5, x_35);
lean_ctor_set(x_27, 1, x_38);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
lean_dec(x_29);
x_39 = lean_array_get_size(x_33);
lean_dec(x_33);
x_40 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_41 = lean_name_append_index_after(x_40, x_39);
x_42 = 0;
x_43 = lean_local_ctx_mk_local_decl(x_32, x_26, x_41, x_22, x_42);
lean_ctor_set(x_27, 7, x_36);
lean_ctor_set(x_27, 5, x_35);
lean_ctor_set(x_27, 1, x_43);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
x_46 = lean_ctor_get(x_27, 2);
x_47 = lean_ctor_get(x_27, 3);
x_48 = lean_ctor_get(x_27, 4);
x_49 = lean_ctor_get(x_27, 5);
x_50 = lean_ctor_get(x_27, 6);
x_51 = lean_ctor_get(x_27, 7);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
lean_inc(x_28);
lean_inc(x_49);
x_52 = lean_array_push(x_49, x_28);
lean_inc(x_28);
x_53 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_51, x_5, x_28);
if (x_30 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
x_54 = 0;
x_55 = lean_local_ctx_mk_local_decl(x_45, x_26, x_29, x_22, x_54);
x_56 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_48);
lean_ctor_set(x_56, 5, x_52);
lean_ctor_set(x_56, 6, x_50);
lean_ctor_set(x_56, 7, x_53);
lean_ctor_set(x_24, 1, x_56);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_29);
x_57 = lean_array_get_size(x_49);
lean_dec(x_49);
x_58 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_59 = lean_name_append_index_after(x_58, x_57);
x_60 = 0;
x_61 = lean_local_ctx_mk_local_decl(x_45, x_26, x_59, x_22, x_60);
x_62 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_46);
lean_ctor_set(x_62, 3, x_47);
lean_ctor_set(x_62, 4, x_48);
lean_ctor_set(x_62, 5, x_52);
lean_ctor_set(x_62, 6, x_50);
lean_ctor_set(x_62, 7, x_53);
lean_ctor_set(x_24, 1, x_62);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_24, 0);
x_64 = lean_ctor_get(x_24, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_24);
lean_inc(x_63);
x_65 = l_Lean_mkFVar(x_63);
x_66 = lean_ctor_get(x_7, 0);
lean_inc(x_66);
lean_dec(x_7);
x_67 = l_Lean_Name_isAnonymous(x_66);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_64, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_64, 7);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 lean_ctor_release(x_64, 4);
 lean_ctor_release(x_64, 5);
 lean_ctor_release(x_64, 6);
 lean_ctor_release(x_64, 7);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
lean_inc(x_65);
lean_inc(x_73);
x_77 = lean_array_push(x_73, x_65);
lean_inc(x_65);
x_78 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_75, x_5, x_65);
if (x_67 == 0)
{
uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_73);
x_79 = 0;
x_80 = lean_local_ctx_mk_local_decl(x_69, x_63, x_66, x_22, x_79);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 8, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_71);
lean_ctor_set(x_81, 4, x_72);
lean_ctor_set(x_81, 5, x_77);
lean_ctor_set(x_81, 6, x_74);
lean_ctor_set(x_81, 7, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
x_83 = lean_array_get_size(x_73);
lean_dec(x_73);
x_84 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_85 = lean_name_append_index_after(x_84, x_83);
x_86 = 0;
x_87 = lean_local_ctx_mk_local_decl(x_69, x_63, x_85, x_22, x_86);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 8, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_68);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_70);
lean_ctor_set(x_88, 3, x_71);
lean_ctor_set(x_88, 4, x_72);
lean_ctor_set(x_88, 5, x_77);
lean_ctor_set(x_88, 6, x_74);
lean_ctor_set(x_88, 7, x_78);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_65);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_7);
lean_dec(x_5);
x_90 = lean_ctor_get(x_19, 0);
lean_inc(x_90);
lean_dec(x_19);
lean_ctor_set(x_12, 0, x_90);
return x_12;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_12, 0);
x_92 = lean_ctor_get(x_12, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_12);
x_93 = lean_expr_eqv(x_1, x_91);
lean_dec(x_1);
if (x_93 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
x_1 = x_91;
x_2 = x_92;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_91);
x_95 = lean_ctor_get(x_92, 7);
lean_inc(x_95);
lean_inc(x_5);
x_96 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_95, x_5);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_97 = lean_ctor_get(x_7, 2);
lean_inc(x_97);
x_98 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_97, x_92);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
lean_inc(x_102);
x_105 = l_Lean_mkFVar(x_102);
x_106 = lean_ctor_get(x_7, 0);
lean_inc(x_106);
lean_dec(x_7);
x_107 = l_Lean_Name_isAnonymous(x_106);
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_103, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 5);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 6);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 7);
lean_inc(x_115);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 lean_ctor_release(x_103, 6);
 lean_ctor_release(x_103, 7);
 x_116 = x_103;
} else {
 lean_dec_ref(x_103);
 x_116 = lean_box(0);
}
lean_inc(x_105);
lean_inc(x_113);
x_117 = lean_array_push(x_113, x_105);
lean_inc(x_105);
x_118 = l_Std_HashMap_insert___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__4(x_115, x_5, x_105);
if (x_107 == 0)
{
uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
x_119 = 0;
x_120 = lean_local_ctx_mk_local_decl(x_109, x_102, x_106, x_99, x_119);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(0, 8, 0);
} else {
 x_121 = x_116;
}
lean_ctor_set(x_121, 0, x_108);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_110);
lean_ctor_set(x_121, 3, x_111);
lean_ctor_set(x_121, 4, x_112);
lean_ctor_set(x_121, 5, x_117);
lean_ctor_set(x_121, 6, x_114);
lean_ctor_set(x_121, 7, x_118);
if (lean_is_scalar(x_104)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_104;
}
lean_ctor_set(x_122, 0, x_105);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_106);
x_123 = lean_array_get_size(x_113);
lean_dec(x_113);
x_124 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_125 = lean_name_append_index_after(x_124, x_123);
x_126 = 0;
x_127 = lean_local_ctx_mk_local_decl(x_109, x_102, x_125, x_99, x_126);
if (lean_is_scalar(x_116)) {
 x_128 = lean_alloc_ctor(0, 8, 0);
} else {
 x_128 = x_116;
}
lean_ctor_set(x_128, 0, x_108);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_110);
lean_ctor_set(x_128, 3, x_111);
lean_ctor_set(x_128, 4, x_112);
lean_ctor_set(x_128, 5, x_117);
lean_ctor_set(x_128, 6, x_114);
lean_ctor_set(x_128, 7, x_118);
if (lean_is_scalar(x_104)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_104;
}
lean_ctor_set(x_129, 0, x_105);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_7);
lean_dec(x_5);
x_130 = lean_ctor_get(x_96, 0);
lean_inc(x_130);
lean_dec(x_96);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_92);
return x_131;
}
}
}
}
}
case 3:
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_1);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
x_134 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_133, x_2);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_expr_update_sort(x_1, x_136);
lean_ctor_set(x_134, 0, x_137);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_134, 0);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_134);
x_140 = lean_expr_update_sort(x_1, x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; uint64_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_142 = lean_ctor_get(x_1, 0);
x_143 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_142);
lean_dec(x_1);
lean_inc(x_142);
x_144 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_142, x_2);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set_uint64(x_148, sizeof(void*)*1, x_143);
x_149 = lean_expr_update_sort(x_148, x_145);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_146);
return x_150;
}
}
case 4:
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_1);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
x_153 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(x_152, x_2);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_expr_update_const(x_1, x_155);
lean_ctor_set(x_153, 0, x_156);
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_153, 0);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_153);
x_159 = lean_expr_update_const(x_1, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; uint64_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_1, 0);
x_162 = lean_ctor_get(x_1, 1);
x_163 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_1);
lean_inc(x_162);
x_164 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__10(x_162, x_2);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set_uint64(x_168, sizeof(void*)*2, x_163);
x_169 = lean_expr_update_const(x_168, x_165);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
}
case 5:
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_1);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_172 = lean_ctor_get(x_1, 0);
x_173 = lean_ctor_get(x_1, 1);
lean_inc(x_172);
x_174 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_172, x_2);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
lean_inc(x_173);
x_177 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_173, x_176);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = lean_expr_update_app(x_1, x_175, x_179);
lean_ctor_set(x_177, 0, x_180);
return x_177;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_177, 0);
x_182 = lean_ctor_get(x_177, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_177);
x_183 = lean_expr_update_app(x_1, x_175, x_181);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; uint64_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_ctor_get(x_1, 0);
x_186 = lean_ctor_get(x_1, 1);
x_187 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_1);
lean_inc(x_185);
x_188 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_185, x_2);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
lean_inc(x_186);
x_191 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_186, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_195, 0, x_185);
lean_ctor_set(x_195, 1, x_186);
lean_ctor_set_uint64(x_195, sizeof(void*)*2, x_187);
x_196 = lean_expr_update_app(x_195, x_189, x_192);
if (lean_is_scalar(x_194)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_194;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_193);
return x_197;
}
}
case 6:
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_1);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; uint64_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_199 = lean_ctor_get(x_1, 1);
x_200 = lean_ctor_get(x_1, 2);
x_201 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_199);
x_202 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_199, x_2);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_200);
x_205 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_200, x_204);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = (uint8_t)((x_201 << 24) >> 61);
x_209 = lean_expr_update_lambda(x_1, x_208, x_203, x_207);
lean_ctor_set(x_205, 0, x_209);
return x_205;
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_205, 0);
x_211 = lean_ctor_get(x_205, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_205);
x_212 = (uint8_t)((x_201 << 24) >> 61);
x_213 = lean_expr_update_lambda(x_1, x_212, x_203, x_210);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint64_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; 
x_215 = lean_ctor_get(x_1, 0);
x_216 = lean_ctor_get(x_1, 1);
x_217 = lean_ctor_get(x_1, 2);
x_218 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_1);
lean_inc(x_216);
x_219 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_216, x_2);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_217);
x_222 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_217, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_226 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set(x_226, 1, x_216);
lean_ctor_set(x_226, 2, x_217);
lean_ctor_set_uint64(x_226, sizeof(void*)*3, x_218);
x_227 = (uint8_t)((x_218 << 24) >> 61);
x_228 = lean_expr_update_lambda(x_226, x_227, x_220, x_223);
if (lean_is_scalar(x_225)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_225;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_224);
return x_229;
}
}
case 7:
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_1);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; uint64_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_231 = lean_ctor_get(x_1, 1);
x_232 = lean_ctor_get(x_1, 2);
x_233 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_231);
x_234 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_231, x_2);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_232);
x_237 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_232, x_236);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; uint8_t x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = (uint8_t)((x_233 << 24) >> 61);
x_241 = lean_expr_update_forall(x_1, x_240, x_235, x_239);
lean_ctor_set(x_237, 0, x_241);
return x_237;
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_237, 0);
x_243 = lean_ctor_get(x_237, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_237);
x_244 = (uint8_t)((x_233 << 24) >> 61);
x_245 = lean_expr_update_forall(x_1, x_244, x_235, x_242);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint64_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; 
x_247 = lean_ctor_get(x_1, 0);
x_248 = lean_ctor_get(x_1, 1);
x_249 = lean_ctor_get(x_1, 2);
x_250 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_1);
lean_inc(x_248);
x_251 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_248, x_2);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_249);
x_254 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_249, x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_258, 0, x_247);
lean_ctor_set(x_258, 1, x_248);
lean_ctor_set(x_258, 2, x_249);
lean_ctor_set_uint64(x_258, sizeof(void*)*3, x_250);
x_259 = (uint8_t)((x_250 << 24) >> 61);
x_260 = lean_expr_update_forall(x_258, x_259, x_252, x_255);
if (lean_is_scalar(x_257)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_257;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_256);
return x_261;
}
}
case 8:
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_1);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_263 = lean_ctor_get(x_1, 1);
x_264 = lean_ctor_get(x_1, 2);
x_265 = lean_ctor_get(x_1, 3);
lean_inc(x_263);
x_266 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_263, x_2);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
lean_inc(x_264);
x_269 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_264, x_268);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_265);
x_272 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_265, x_271);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_expr_update_let(x_1, x_267, x_270, x_274);
lean_ctor_set(x_272, 0, x_275);
return x_272;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_272, 0);
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_272);
x_278 = lean_expr_update_let(x_1, x_267, x_270, x_276);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint64_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_280 = lean_ctor_get(x_1, 0);
x_281 = lean_ctor_get(x_1, 1);
x_282 = lean_ctor_get(x_1, 2);
x_283 = lean_ctor_get(x_1, 3);
x_284 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_1);
lean_inc(x_281);
x_285 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_281, x_2);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_inc(x_282);
x_288 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_282, x_287);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_283);
x_291 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_283, x_290);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_294 = x_291;
} else {
 lean_dec_ref(x_291);
 x_294 = lean_box(0);
}
x_295 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_295, 0, x_280);
lean_ctor_set(x_295, 1, x_281);
lean_ctor_set(x_295, 2, x_282);
lean_ctor_set(x_295, 3, x_283);
lean_ctor_set_uint64(x_295, sizeof(void*)*4, x_284);
x_296 = lean_expr_update_let(x_295, x_286, x_289, x_292);
if (lean_is_scalar(x_294)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_294;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_293);
return x_297;
}
}
case 10:
{
uint8_t x_298; 
x_298 = !lean_is_exclusive(x_1);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = lean_ctor_get(x_1, 1);
lean_inc(x_299);
x_300 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_299, x_2);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_300, 0);
x_303 = lean_expr_update_mdata(x_1, x_302);
lean_ctor_set(x_300, 0, x_303);
return x_300;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_300, 0);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_300);
x_306 = lean_expr_update_mdata(x_1, x_304);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; uint64_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_308 = lean_ctor_get(x_1, 0);
x_309 = lean_ctor_get(x_1, 1);
x_310 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_1);
lean_inc(x_309);
x_311 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_309, x_2);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_314 = x_311;
} else {
 lean_dec_ref(x_311);
 x_314 = lean_box(0);
}
x_315 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_315, 0, x_308);
lean_ctor_set(x_315, 1, x_309);
lean_ctor_set_uint64(x_315, sizeof(void*)*2, x_310);
x_316 = lean_expr_update_mdata(x_315, x_312);
if (lean_is_scalar(x_314)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_314;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_313);
return x_317;
}
}
case 11:
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_1);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_319 = lean_ctor_get(x_1, 2);
lean_inc(x_319);
x_320 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_319, x_2);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_320, 0);
x_323 = lean_expr_update_proj(x_1, x_322);
lean_ctor_set(x_320, 0, x_323);
return x_320;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_320, 0);
x_325 = lean_ctor_get(x_320, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_320);
x_326 = lean_expr_update_proj(x_1, x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint64_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_328 = lean_ctor_get(x_1, 0);
x_329 = lean_ctor_get(x_1, 1);
x_330 = lean_ctor_get(x_1, 2);
x_331 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_1);
lean_inc(x_330);
x_332 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_330, x_2);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_335 = x_332;
} else {
 lean_dec_ref(x_332);
 x_335 = lean_box(0);
}
x_336 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_336, 0, x_328);
lean_ctor_set(x_336, 1, x_329);
lean_ctor_set(x_336, 2, x_330);
lean_ctor_set_uint64(x_336, sizeof(void*)*3, x_331);
x_337 = lean_expr_update_proj(x_336, x_333);
if (lean_is_scalar(x_335)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_335;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_334);
return x_338;
}
}
default: 
{
lean_object* x_339; 
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_1);
lean_ctor_set(x_339, 1, x_2);
return x_339;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_7 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
x_24 = l_Lean_Meta_abstractMVars___closed__1;
lean_inc(x_16);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set(x_25, 7, x_24);
x_26 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_8, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
x_39 = lean_st_ref_take(x_5, x_19);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_40, 2);
lean_dec(x_43);
lean_ctor_set(x_40, 2, x_38);
x_44 = lean_st_ref_set(x_5, x_40, x_41);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_28, 2);
lean_inc(x_46);
x_47 = lean_st_ref_get(x_5, x_45);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_3, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_46, sizeof(void*)*8);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_46, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_46, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_46, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_46, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 7);
lean_inc(x_61);
lean_dec(x_46);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_50, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_52);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_52, 7);
lean_dec(x_65);
x_66 = lean_ctor_get(x_52, 6);
lean_dec(x_66);
x_67 = lean_ctor_get(x_52, 5);
lean_dec(x_67);
x_68 = lean_ctor_get(x_52, 4);
lean_dec(x_68);
x_69 = lean_ctor_get(x_52, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_52, 2);
lean_dec(x_70);
x_71 = lean_ctor_get(x_52, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_52, 0);
lean_dec(x_72);
lean_ctor_set(x_52, 7, x_61);
lean_ctor_set(x_52, 6, x_60);
lean_ctor_set(x_52, 5, x_59);
lean_ctor_set(x_52, 4, x_58);
lean_ctor_set(x_52, 3, x_57);
lean_ctor_set(x_52, 2, x_56);
lean_ctor_set(x_52, 1, x_55);
lean_ctor_set(x_52, 0, x_54);
x_73 = lean_st_ref_set(x_3, x_50, x_53);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_29 = x_74;
goto block_37;
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get_uint8(x_52, sizeof(void*)*8);
lean_dec(x_52);
x_76 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_76, 0, x_54);
lean_ctor_set(x_76, 1, x_55);
lean_ctor_set(x_76, 2, x_56);
lean_ctor_set(x_76, 3, x_57);
lean_ctor_set(x_76, 4, x_58);
lean_ctor_set(x_76, 5, x_59);
lean_ctor_set(x_76, 6, x_60);
lean_ctor_set(x_76, 7, x_61);
lean_ctor_set_uint8(x_76, sizeof(void*)*8, x_75);
lean_ctor_set(x_50, 0, x_76);
x_77 = lean_st_ref_set(x_3, x_50, x_53);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_29 = x_78;
goto block_37;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_50, 1);
x_80 = lean_ctor_get(x_50, 2);
x_81 = lean_ctor_get(x_50, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_50);
x_82 = lean_ctor_get_uint8(x_52, sizeof(void*)*8);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 lean_ctor_release(x_52, 7);
 x_83 = x_52;
} else {
 lean_dec_ref(x_52);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 8, 1);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_54);
lean_ctor_set(x_84, 1, x_55);
lean_ctor_set(x_84, 2, x_56);
lean_ctor_set(x_84, 3, x_57);
lean_ctor_set(x_84, 4, x_58);
lean_ctor_set(x_84, 5, x_59);
lean_ctor_set(x_84, 6, x_60);
lean_ctor_set(x_84, 7, x_61);
lean_ctor_set_uint8(x_84, sizeof(void*)*8, x_82);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_81);
x_86 = lean_st_ref_set(x_3, x_85, x_53);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_29 = x_87;
goto block_37;
}
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_49, 1);
lean_inc(x_88);
lean_dec(x_49);
x_89 = !lean_is_exclusive(x_46);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_50);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_50, 0);
lean_dec(x_91);
x_92 = 1;
lean_ctor_set_uint8(x_46, sizeof(void*)*8, x_92);
lean_ctor_set(x_50, 0, x_46);
x_93 = lean_st_ref_set(x_3, x_50, x_88);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_29 = x_94;
goto block_37;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_50, 1);
x_96 = lean_ctor_get(x_50, 2);
x_97 = lean_ctor_get(x_50, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_50);
x_98 = 1;
lean_ctor_set_uint8(x_46, sizeof(void*)*8, x_98);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_46);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
x_100 = lean_st_ref_set(x_3, x_99, x_88);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_29 = x_101;
goto block_37;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_102 = lean_ctor_get(x_46, 0);
x_103 = lean_ctor_get(x_46, 1);
x_104 = lean_ctor_get(x_46, 2);
x_105 = lean_ctor_get(x_46, 3);
x_106 = lean_ctor_get(x_46, 4);
x_107 = lean_ctor_get(x_46, 5);
x_108 = lean_ctor_get(x_46, 6);
x_109 = lean_ctor_get(x_46, 7);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_46);
x_110 = lean_ctor_get(x_50, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_50, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_50, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 x_113 = x_50;
} else {
 lean_dec_ref(x_50);
 x_113 = lean_box(0);
}
x_114 = 1;
x_115 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_115, 0, x_102);
lean_ctor_set(x_115, 1, x_103);
lean_ctor_set(x_115, 2, x_104);
lean_ctor_set(x_115, 3, x_105);
lean_ctor_set(x_115, 4, x_106);
lean_ctor_set(x_115, 5, x_107);
lean_ctor_set(x_115, 6, x_108);
lean_ctor_set(x_115, 7, x_109);
lean_ctor_set_uint8(x_115, sizeof(void*)*8, x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_110);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_112);
x_117 = lean_st_ref_set(x_3, x_116, x_88);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_29 = x_118;
goto block_37;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_119 = lean_ctor_get(x_40, 0);
x_120 = lean_ctor_get(x_40, 1);
x_121 = lean_ctor_get(x_40, 3);
x_122 = lean_ctor_get(x_40, 4);
x_123 = lean_ctor_get(x_40, 5);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_40);
x_124 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_38);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_122);
lean_ctor_set(x_124, 5, x_123);
x_125 = lean_st_ref_set(x_5, x_124, x_41);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get(x_28, 2);
lean_inc(x_127);
x_128 = lean_st_ref_get(x_5, x_126);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_3, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get_uint8(x_127, sizeof(void*)*8);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec(x_130);
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_127, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_127, 6);
lean_inc(x_141);
x_142 = lean_ctor_get(x_127, 7);
lean_inc(x_142);
lean_dec(x_127);
x_143 = lean_ctor_get(x_131, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_131, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_131, 3);
lean_inc(x_145);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_146 = x_131;
} else {
 lean_dec_ref(x_131);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get_uint8(x_133, sizeof(void*)*8);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 lean_ctor_release(x_133, 6);
 lean_ctor_release(x_133, 7);
 x_148 = x_133;
} else {
 lean_dec_ref(x_133);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 8, 1);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set(x_149, 2, x_137);
lean_ctor_set(x_149, 3, x_138);
lean_ctor_set(x_149, 4, x_139);
lean_ctor_set(x_149, 5, x_140);
lean_ctor_set(x_149, 6, x_141);
lean_ctor_set(x_149, 7, x_142);
lean_ctor_set_uint8(x_149, sizeof(void*)*8, x_147);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 4, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_143);
lean_ctor_set(x_150, 2, x_144);
lean_ctor_set(x_150, 3, x_145);
x_151 = lean_st_ref_set(x_3, x_150, x_134);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_29 = x_152;
goto block_37;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_153 = lean_ctor_get(x_130, 1);
lean_inc(x_153);
lean_dec(x_130);
x_154 = lean_ctor_get(x_127, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_127, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_127, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_127, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_127, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_127, 5);
lean_inc(x_159);
x_160 = lean_ctor_get(x_127, 6);
lean_inc(x_160);
x_161 = lean_ctor_get(x_127, 7);
lean_inc(x_161);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 lean_ctor_release(x_127, 6);
 lean_ctor_release(x_127, 7);
 x_162 = x_127;
} else {
 lean_dec_ref(x_127);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_131, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_131, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_131, 3);
lean_inc(x_165);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_166 = x_131;
} else {
 lean_dec_ref(x_131);
 x_166 = lean_box(0);
}
x_167 = 1;
if (lean_is_scalar(x_162)) {
 x_168 = lean_alloc_ctor(0, 8, 1);
} else {
 x_168 = x_162;
}
lean_ctor_set(x_168, 0, x_154);
lean_ctor_set(x_168, 1, x_155);
lean_ctor_set(x_168, 2, x_156);
lean_ctor_set(x_168, 3, x_157);
lean_ctor_set(x_168, 4, x_158);
lean_ctor_set(x_168, 5, x_159);
lean_ctor_set(x_168, 6, x_160);
lean_ctor_set(x_168, 7, x_161);
lean_ctor_set_uint8(x_168, sizeof(void*)*8, x_167);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 4, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 2, x_164);
lean_ctor_set(x_169, 3, x_165);
x_170 = lean_st_ref_set(x_3, x_169, x_153);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_29 = x_171;
goto block_37;
}
}
block_37:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 5);
lean_inc(x_31);
x_32 = l_Lean_LocalContext_mkLambda(x_30, x_31, x_27);
x_33 = lean_ctor_get(x_28, 4);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_array_get_size(x_31);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_32);
if (lean_is_scalar(x_20)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_20;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
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
l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3 = _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3);
l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4 = _init_l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4);
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
