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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_State_emap___default___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult;
static lean_object* l_Lean_Meta_AbstractMVars_State_lmap___default___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
static uint64_t l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instBEqAbstractMVarsResult___closed__1;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_abstractMVars___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_mkFreshId(lean_object*);
lean_object* l_Lean_Meta_lambdaMetaTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(lean_object*);
extern lean_object* l_Lean_instHashableMVarId;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_emap___default;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1___boxed(lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_instBEqMVarId;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_nextParamIdx___default;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__3;
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_lmap___default___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Meta_AbstractMVars_State_emap___default___spec__1(lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_lmap___default;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedAbstractMVarsResult___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqAbstractMVarsResult;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_paramNames___default;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_AbstractMVars_State_fvars___default;
lean_object* lean_expr_update_const(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41_(lean_object* x_1, lean_object* x_2) {
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
x_14 = l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____spec__1(x_3, x_6, lean_box(0), x_3, x_6, x_13);
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
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_AbstractMVars___hyg_41____boxed), 2, 0);
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
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_lmap___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_lmap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_AbstractMVars_State_lmap___default___closed__1;
return x_1;
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
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_emap___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_AbstractMVars_State_emap___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_AbstractMVars_State_emap___default___closed__1;
return x_1;
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
x_5 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(x_2);
x_6 = (size_t)x_5;
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
static lean_object* _init_l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_abstMVar");
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
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
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
x_107 = l_Lean_instBEqMVarId;
x_108 = l_Lean_instHashableMVarId;
lean_inc(x_103);
x_109 = l_Std_HashMap_insert___rarg(x_107, x_108, x_85, x_78, x_103);
lean_ctor_set(x_2, 6, x_109);
lean_ctor_set(x_2, 4, x_106);
lean_ctor_set(x_2, 3, x_105);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_2);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
x_111 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars___closed__2;
lean_inc(x_82);
x_112 = lean_name_mk_numeral(x_111, x_82);
lean_inc(x_112);
x_113 = l_Lean_mkLevelParam(x_112);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_add(x_82, x_114);
lean_dec(x_82);
x_116 = lean_array_push(x_83, x_112);
x_117 = l_Lean_instBEqMVarId;
x_118 = l_Lean_instHashableMVarId;
lean_inc(x_113);
x_119 = l_Std_HashMap_insert___rarg(x_117, x_118, x_85, x_78, x_113);
x_120 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_120, 0, x_79);
lean_ctor_set(x_120, 1, x_80);
lean_ctor_set(x_120, 2, x_81);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 4, x_116);
lean_ctor_set(x_120, 5, x_84);
lean_ctor_set(x_120, 6, x_119);
lean_ctor_set(x_120, 7, x_86);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
x_122 = lean_ctor_get(x_91, 0);
lean_inc(x_122);
lean_dec(x_91);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_2);
return x_123;
}
}
}
default: 
{
lean_object* x_124; 
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_2);
return x_124;
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
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_7, x_10);
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
x_22 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_18, x_21);
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
x_1 = lean_mk_string("x");
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 7);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_8);
x_14 = l_Lean_MetavarContext_getDecl(x_8, x_5);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_19 = l_Lean_MetavarContext_instantiateMVars(x_8, x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_expr_eqv(x_1, x_21);
lean_dec(x_1);
if (x_23 == 0)
{
uint8_t x_24; 
lean_free_object(x_19);
lean_dec(x_14);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_2, 7);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 6);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_2, 0);
lean_dec(x_32);
lean_ctor_set(x_2, 2, x_22);
x_1 = x_21;
goto _start;
}
else
{
lean_object* x_34; 
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_7);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_9);
lean_ctor_set(x_34, 4, x_10);
lean_ctor_set(x_34, 5, x_11);
lean_ctor_set(x_34, 6, x_12);
lean_ctor_set(x_34, 7, x_13);
x_1 = x_21;
x_2 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_5);
x_36 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(x_13, x_5);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_free_object(x_19);
x_37 = lean_ctor_get(x_14, 2);
lean_inc(x_37);
x_38 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_37, x_2);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_45 = l_Lean_mkFVar(x_43);
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
lean_dec(x_14);
x_47 = l_Lean_Name_isAnonymous(x_46);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_44, 1);
x_50 = lean_ctor_get(x_44, 5);
x_51 = lean_ctor_get(x_44, 7);
lean_inc(x_45);
x_52 = lean_array_push(x_50, x_45);
x_53 = l_Lean_instBEqMVarId;
x_54 = l_Lean_instHashableMVarId;
lean_inc(x_45);
x_55 = l_Std_HashMap_insert___rarg(x_53, x_54, x_51, x_5, x_45);
if (x_47 == 0)
{
uint8_t x_56; lean_object* x_57; 
lean_dec(x_11);
x_56 = 0;
x_57 = lean_local_ctx_mk_local_decl(x_49, x_43, x_46, x_39, x_56);
lean_ctor_set(x_44, 7, x_55);
lean_ctor_set(x_44, 5, x_52);
lean_ctor_set(x_44, 1, x_57);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
lean_dec(x_46);
x_58 = lean_array_get_size(x_11);
lean_dec(x_11);
x_59 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_60 = lean_name_append_index_after(x_59, x_58);
x_61 = 0;
x_62 = lean_local_ctx_mk_local_decl(x_49, x_43, x_60, x_39, x_61);
lean_ctor_set(x_44, 7, x_55);
lean_ctor_set(x_44, 5, x_52);
lean_ctor_set(x_44, 1, x_62);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_ctor_get(x_44, 0);
x_64 = lean_ctor_get(x_44, 1);
x_65 = lean_ctor_get(x_44, 2);
x_66 = lean_ctor_get(x_44, 3);
x_67 = lean_ctor_get(x_44, 4);
x_68 = lean_ctor_get(x_44, 5);
x_69 = lean_ctor_get(x_44, 6);
x_70 = lean_ctor_get(x_44, 7);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_44);
lean_inc(x_45);
x_71 = lean_array_push(x_68, x_45);
x_72 = l_Lean_instBEqMVarId;
x_73 = l_Lean_instHashableMVarId;
lean_inc(x_45);
x_74 = l_Std_HashMap_insert___rarg(x_72, x_73, x_70, x_5, x_45);
if (x_47 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_11);
x_75 = 0;
x_76 = lean_local_ctx_mk_local_decl(x_64, x_43, x_46, x_39, x_75);
x_77 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_66);
lean_ctor_set(x_77, 4, x_67);
lean_ctor_set(x_77, 5, x_71);
lean_ctor_set(x_77, 6, x_69);
lean_ctor_set(x_77, 7, x_74);
lean_ctor_set(x_41, 1, x_77);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_46);
x_78 = lean_array_get_size(x_11);
lean_dec(x_11);
x_79 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_80 = lean_name_append_index_after(x_79, x_78);
x_81 = 0;
x_82 = lean_local_ctx_mk_local_decl(x_64, x_43, x_80, x_39, x_81);
x_83 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_83, 0, x_63);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_65);
lean_ctor_set(x_83, 3, x_66);
lean_ctor_set(x_83, 4, x_67);
lean_ctor_set(x_83, 5, x_71);
lean_ctor_set(x_83, 6, x_69);
lean_ctor_set(x_83, 7, x_74);
lean_ctor_set(x_41, 1, x_83);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_84 = lean_ctor_get(x_41, 0);
x_85 = lean_ctor_get(x_41, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_41);
lean_inc(x_84);
x_86 = l_Lean_mkFVar(x_84);
x_87 = lean_ctor_get(x_14, 0);
lean_inc(x_87);
lean_dec(x_14);
x_88 = l_Lean_Name_isAnonymous(x_87);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_85, 6);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 7);
lean_inc(x_96);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 lean_ctor_release(x_85, 5);
 lean_ctor_release(x_85, 6);
 lean_ctor_release(x_85, 7);
 x_97 = x_85;
} else {
 lean_dec_ref(x_85);
 x_97 = lean_box(0);
}
lean_inc(x_86);
x_98 = lean_array_push(x_94, x_86);
x_99 = l_Lean_instBEqMVarId;
x_100 = l_Lean_instHashableMVarId;
lean_inc(x_86);
x_101 = l_Std_HashMap_insert___rarg(x_99, x_100, x_96, x_5, x_86);
if (x_88 == 0)
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_11);
x_102 = 0;
x_103 = lean_local_ctx_mk_local_decl(x_90, x_84, x_87, x_39, x_102);
if (lean_is_scalar(x_97)) {
 x_104 = lean_alloc_ctor(0, 8, 0);
} else {
 x_104 = x_97;
}
lean_ctor_set(x_104, 0, x_89);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_91);
lean_ctor_set(x_104, 3, x_92);
lean_ctor_set(x_104, 4, x_93);
lean_ctor_set(x_104, 5, x_98);
lean_ctor_set(x_104, 6, x_95);
lean_ctor_set(x_104, 7, x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_87);
x_106 = lean_array_get_size(x_11);
lean_dec(x_11);
x_107 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_108 = lean_name_append_index_after(x_107, x_106);
x_109 = 0;
x_110 = lean_local_ctx_mk_local_decl(x_90, x_84, x_108, x_39, x_109);
if (lean_is_scalar(x_97)) {
 x_111 = lean_alloc_ctor(0, 8, 0);
} else {
 x_111 = x_97;
}
lean_ctor_set(x_111, 0, x_89);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_91);
lean_ctor_set(x_111, 3, x_92);
lean_ctor_set(x_111, 4, x_93);
lean_ctor_set(x_111, 5, x_98);
lean_ctor_set(x_111, 6, x_95);
lean_ctor_set(x_111, 7, x_101);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_86);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
x_113 = lean_ctor_get(x_36, 0);
lean_inc(x_113);
lean_dec(x_36);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_113);
return x_19;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_19, 0);
x_115 = lean_ctor_get(x_19, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_19);
x_116 = lean_expr_eqv(x_1, x_114);
lean_dec(x_1);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_14);
lean_dec(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 x_117 = x_2;
} else {
 lean_dec_ref(x_2);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 8, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_6);
lean_ctor_set(x_118, 1, x_7);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_9);
lean_ctor_set(x_118, 4, x_10);
lean_ctor_set(x_118, 5, x_11);
lean_ctor_set(x_118, 6, x_12);
lean_ctor_set(x_118, 7, x_13);
x_1 = x_114;
x_2 = x_118;
goto _start;
}
else
{
lean_object* x_120; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_5);
x_120 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__1(x_13, x_5);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_121 = lean_ctor_get(x_14, 2);
lean_inc(x_121);
x_122 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_121, x_2);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Meta_AbstractMVars_mkFreshFVarId(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
lean_inc(x_126);
x_129 = l_Lean_mkFVar(x_126);
x_130 = lean_ctor_get(x_14, 0);
lean_inc(x_130);
lean_dec(x_14);
x_131 = l_Lean_Name_isAnonymous(x_130);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 5);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 6);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 7);
lean_inc(x_139);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 lean_ctor_release(x_127, 6);
 lean_ctor_release(x_127, 7);
 x_140 = x_127;
} else {
 lean_dec_ref(x_127);
 x_140 = lean_box(0);
}
lean_inc(x_129);
x_141 = lean_array_push(x_137, x_129);
x_142 = l_Lean_instBEqMVarId;
x_143 = l_Lean_instHashableMVarId;
lean_inc(x_129);
x_144 = l_Std_HashMap_insert___rarg(x_142, x_143, x_139, x_5, x_129);
if (x_131 == 0)
{
uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_11);
x_145 = 0;
x_146 = lean_local_ctx_mk_local_decl(x_133, x_126, x_130, x_123, x_145);
if (lean_is_scalar(x_140)) {
 x_147 = lean_alloc_ctor(0, 8, 0);
} else {
 x_147 = x_140;
}
lean_ctor_set(x_147, 0, x_132);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_134);
lean_ctor_set(x_147, 3, x_135);
lean_ctor_set(x_147, 4, x_136);
lean_ctor_set(x_147, 5, x_141);
lean_ctor_set(x_147, 6, x_138);
lean_ctor_set(x_147, 7, x_144);
if (lean_is_scalar(x_128)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_128;
}
lean_ctor_set(x_148, 0, x_129);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_130);
x_149 = lean_array_get_size(x_11);
lean_dec(x_11);
x_150 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__2;
x_151 = lean_name_append_index_after(x_150, x_149);
x_152 = 0;
x_153 = lean_local_ctx_mk_local_decl(x_133, x_126, x_151, x_123, x_152);
if (lean_is_scalar(x_140)) {
 x_154 = lean_alloc_ctor(0, 8, 0);
} else {
 x_154 = x_140;
}
lean_ctor_set(x_154, 0, x_132);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_134);
lean_ctor_set(x_154, 3, x_135);
lean_ctor_set(x_154, 4, x_136);
lean_ctor_set(x_154, 5, x_141);
lean_ctor_set(x_154, 6, x_138);
lean_ctor_set(x_154, 7, x_144);
if (lean_is_scalar(x_128)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_128;
}
lean_ctor_set(x_155, 0, x_129);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
x_156 = lean_ctor_get(x_120, 0);
lean_inc(x_156);
lean_dec(x_120);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_2);
return x_157;
}
}
}
}
}
case 3:
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_1);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_159, x_2);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_expr_update_sort(x_1, x_162);
lean_ctor_set(x_160, 0, x_163);
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_160, 0);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_160);
x_166 = lean_expr_update_sort(x_1, x_164);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; uint64_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_1, 0);
x_169 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_168);
lean_dec(x_1);
lean_inc(x_168);
x_170 = l___private_Lean_Meta_AbstractMVars_0__Lean_Meta_AbstractMVars_abstractLevelMVars(x_168, x_2);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_174, 0, x_168);
lean_ctor_set_uint64(x_174, sizeof(void*)*1, x_169);
x_175 = lean_expr_update_sort(x_174, x_171);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
}
case 4:
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_1);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_1, 1);
lean_inc(x_178);
x_179 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_178, x_2);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_expr_update_const(x_1, x_181);
lean_ctor_set(x_179, 0, x_182);
return x_179;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_179, 0);
x_184 = lean_ctor_get(x_179, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_179);
x_185 = lean_expr_update_const(x_1, x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; uint64_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_187 = lean_ctor_get(x_1, 0);
x_188 = lean_ctor_get(x_1, 1);
x_189 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_1);
lean_inc(x_188);
x_190 = l_List_mapM___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__3(x_188, x_2);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_194 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_188);
lean_ctor_set_uint64(x_194, sizeof(void*)*2, x_189);
x_195 = lean_expr_update_const(x_194, x_191);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
return x_196;
}
}
case 5:
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_1);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_198 = lean_ctor_get(x_1, 0);
x_199 = lean_ctor_get(x_1, 1);
lean_inc(x_198);
x_200 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_198, x_2);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_199);
x_203 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_199, x_202);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_expr_update_app(x_1, x_201, x_205);
lean_ctor_set(x_203, 0, x_206);
return x_203;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_203, 0);
x_208 = lean_ctor_get(x_203, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_203);
x_209 = lean_expr_update_app(x_1, x_201, x_207);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; uint64_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_211 = lean_ctor_get(x_1, 0);
x_212 = lean_ctor_get(x_1, 1);
x_213 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_1);
lean_inc(x_211);
x_214 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_211, x_2);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
lean_inc(x_212);
x_217 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_212, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_221, 0, x_211);
lean_ctor_set(x_221, 1, x_212);
lean_ctor_set_uint64(x_221, sizeof(void*)*2, x_213);
x_222 = lean_expr_update_app(x_221, x_215, x_218);
if (lean_is_scalar(x_220)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_220;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_219);
return x_223;
}
}
case 6:
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_1);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; uint64_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_225 = lean_ctor_get(x_1, 1);
x_226 = lean_ctor_get(x_1, 2);
x_227 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_225);
x_228 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_225, x_2);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_226);
x_231 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_226, x_230);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = (uint8_t)((x_227 << 24) >> 61);
x_235 = lean_expr_update_lambda(x_1, x_234, x_229, x_233);
lean_ctor_set(x_231, 0, x_235);
return x_231;
}
else
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_231, 0);
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_231);
x_238 = (uint8_t)((x_227 << 24) >> 61);
x_239 = lean_expr_update_lambda(x_1, x_238, x_229, x_236);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint64_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; 
x_241 = lean_ctor_get(x_1, 0);
x_242 = lean_ctor_get(x_1, 1);
x_243 = lean_ctor_get(x_1, 2);
x_244 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_1);
lean_inc(x_242);
x_245 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_242, x_2);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
lean_inc(x_243);
x_248 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_243, x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_251 = x_248;
} else {
 lean_dec_ref(x_248);
 x_251 = lean_box(0);
}
x_252 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_252, 0, x_241);
lean_ctor_set(x_252, 1, x_242);
lean_ctor_set(x_252, 2, x_243);
lean_ctor_set_uint64(x_252, sizeof(void*)*3, x_244);
x_253 = (uint8_t)((x_244 << 24) >> 61);
x_254 = lean_expr_update_lambda(x_252, x_253, x_246, x_249);
if (lean_is_scalar(x_251)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_251;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_250);
return x_255;
}
}
case 7:
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_1);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; uint64_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_257 = lean_ctor_get(x_1, 1);
x_258 = lean_ctor_get(x_1, 2);
x_259 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_257);
x_260 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_257, x_2);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_258);
x_263 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_258, x_262);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = (uint8_t)((x_259 << 24) >> 61);
x_267 = lean_expr_update_forall(x_1, x_266, x_261, x_265);
lean_ctor_set(x_263, 0, x_267);
return x_263;
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_263, 0);
x_269 = lean_ctor_get(x_263, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_263);
x_270 = (uint8_t)((x_259 << 24) >> 61);
x_271 = lean_expr_update_forall(x_1, x_270, x_261, x_268);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_269);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint64_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; 
x_273 = lean_ctor_get(x_1, 0);
x_274 = lean_ctor_get(x_1, 1);
x_275 = lean_ctor_get(x_1, 2);
x_276 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_1);
lean_inc(x_274);
x_277 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_274, x_2);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
lean_inc(x_275);
x_280 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_275, x_279);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
x_284 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_284, 0, x_273);
lean_ctor_set(x_284, 1, x_274);
lean_ctor_set(x_284, 2, x_275);
lean_ctor_set_uint64(x_284, sizeof(void*)*3, x_276);
x_285 = (uint8_t)((x_276 << 24) >> 61);
x_286 = lean_expr_update_forall(x_284, x_285, x_278, x_281);
if (lean_is_scalar(x_283)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_283;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_282);
return x_287;
}
}
case 8:
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_1);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_289 = lean_ctor_get(x_1, 1);
x_290 = lean_ctor_get(x_1, 2);
x_291 = lean_ctor_get(x_1, 3);
lean_inc(x_289);
x_292 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_289, x_2);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
lean_inc(x_290);
x_295 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_290, x_294);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
lean_inc(x_291);
x_298 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_291, x_297);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_298, 0);
x_301 = lean_expr_update_let(x_1, x_293, x_296, x_300);
lean_ctor_set(x_298, 0, x_301);
return x_298;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_298, 0);
x_303 = lean_ctor_get(x_298, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_298);
x_304 = lean_expr_update_let(x_1, x_293, x_296, x_302);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint64_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_306 = lean_ctor_get(x_1, 0);
x_307 = lean_ctor_get(x_1, 1);
x_308 = lean_ctor_get(x_1, 2);
x_309 = lean_ctor_get(x_1, 3);
x_310 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_1);
lean_inc(x_307);
x_311 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_307, x_2);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
lean_inc(x_308);
x_314 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_308, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
lean_inc(x_309);
x_317 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_309, x_316);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
 x_320 = lean_box(0);
}
x_321 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_321, 0, x_306);
lean_ctor_set(x_321, 1, x_307);
lean_ctor_set(x_321, 2, x_308);
lean_ctor_set(x_321, 3, x_309);
lean_ctor_set_uint64(x_321, sizeof(void*)*4, x_310);
x_322 = lean_expr_update_let(x_321, x_312, x_315, x_318);
if (lean_is_scalar(x_320)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_320;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_319);
return x_323;
}
}
case 10:
{
uint8_t x_324; 
x_324 = !lean_is_exclusive(x_1);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_325 = lean_ctor_get(x_1, 1);
lean_inc(x_325);
x_326 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_325, x_2);
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_326, 0);
x_329 = lean_expr_update_mdata(x_1, x_328);
lean_ctor_set(x_326, 0, x_329);
return x_326;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_326, 0);
x_331 = lean_ctor_get(x_326, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_326);
x_332 = lean_expr_update_mdata(x_1, x_330);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; uint64_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_334 = lean_ctor_get(x_1, 0);
x_335 = lean_ctor_get(x_1, 1);
x_336 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_1);
lean_inc(x_335);
x_337 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_335, x_2);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_341, 0, x_334);
lean_ctor_set(x_341, 1, x_335);
lean_ctor_set_uint64(x_341, sizeof(void*)*2, x_336);
x_342 = lean_expr_update_mdata(x_341, x_338);
if (lean_is_scalar(x_340)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_340;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_339);
return x_343;
}
}
case 11:
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_1);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_345 = lean_ctor_get(x_1, 2);
lean_inc(x_345);
x_346 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_345, x_2);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = lean_expr_update_proj(x_1, x_348);
lean_ctor_set(x_346, 0, x_349);
return x_346;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_346, 0);
x_351 = lean_ctor_get(x_346, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_346);
x_352 = lean_expr_update_proj(x_1, x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint64_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_354 = lean_ctor_get(x_1, 0);
x_355 = lean_ctor_get(x_1, 1);
x_356 = lean_ctor_get(x_1, 2);
x_357 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_1);
lean_inc(x_356);
x_358 = l_Lean_Meta_AbstractMVars_abstractExprMVars(x_356, x_2);
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
x_362 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_362, 0, x_354);
lean_ctor_set(x_362, 1, x_355);
lean_ctor_set(x_362, 2, x_356);
lean_ctor_set_uint64(x_362, sizeof(void*)*3, x_357);
x_363 = lean_expr_update_proj(x_362, x_359);
if (lean_is_scalar(x_361)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_361;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_360);
return x_364;
}
}
default: 
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_1);
lean_ctor_set(x_365, 1, x_2);
return x_365;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Meta_AbstractMVars_abstractExprMVars___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_instantiateMVars(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
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
lean_inc(x_16);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_30, 2);
lean_dec(x_33);
lean_ctor_set(x_30, 2, x_28);
x_34 = lean_st_ref_set(x_5, x_30, x_31);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_27, 2);
lean_inc(x_36);
x_37 = l_Lean_Meta_setMCtx(x_36, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_27, 5);
lean_inc(x_41);
x_42 = l_Lean_LocalContext_mkLambda(x_40, x_41, x_26);
x_43 = lean_ctor_get(x_27, 4);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_array_get_size(x_41);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_37, 0, x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_30, 0);
x_55 = lean_ctor_get(x_30, 1);
x_56 = lean_ctor_get(x_30, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_30);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_5, x_57, x_31);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_27, 2);
lean_inc(x_60);
x_61 = l_Lean_Meta_setMCtx(x_60, x_2, x_3, x_4, x_5, x_59);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_27, 5);
lean_inc(x_65);
x_66 = l_Lean_LocalContext_mkLambda(x_64, x_65, x_26);
x_67 = lean_ctor_get(x_27, 4);
lean_inc(x_67);
lean_dec(x_27);
x_68 = lean_array_get_size(x_65);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_66);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_7);
if (x_71 == 0)
{
return x_7;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_ctor_get(x_7, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_7);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Lean_Meta_mkFreshLevelMVar(x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_2 + x_17;
x_19 = x_15;
x_20 = lean_array_uset(x_13, x_2, x_19);
x_2 = x_18;
x_3 = x_20;
x_8 = x_16;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_openAbstractMVarsResult___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_openAbstractMVarsResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
lean_inc(x_7);
x_10 = x_7;
x_11 = lean_box_usize(x_9);
x_12 = l_Lean_Meta_openAbstractMVarsResult___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed), 8, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = x_13;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_apply_5(x_14, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_7, x_16, x_18);
lean_dec(x_16);
lean_dec(x_7);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_lambdaMetaTelescope(x_19, x_21, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_21);
lean_dec(x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AbstractMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
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
l_Lean_Meta_AbstractMVars_State_lmap___default___closed__1 = _init_l_Lean_Meta_AbstractMVars_State_lmap___default___closed__1();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_lmap___default___closed__1);
l_Lean_Meta_AbstractMVars_State_lmap___default = _init_l_Lean_Meta_AbstractMVars_State_lmap___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_lmap___default);
l_Lean_Meta_AbstractMVars_State_emap___default___closed__1 = _init_l_Lean_Meta_AbstractMVars_State_emap___default___closed__1();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_emap___default___closed__1);
l_Lean_Meta_AbstractMVars_State_emap___default = _init_l_Lean_Meta_AbstractMVars_State_emap___default();
lean_mark_persistent(l_Lean_Meta_AbstractMVars_State_emap___default);
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
l_Lean_Meta_openAbstractMVarsResult___boxed__const__1 = _init_l_Lean_Meta_openAbstractMVarsResult___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_openAbstractMVarsResult___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
