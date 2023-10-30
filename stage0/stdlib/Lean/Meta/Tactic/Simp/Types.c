// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Types
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.CongrTheorems Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems
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
static lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__3;
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedResult;
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_simpTheorems___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedStep;
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_result(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__2;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_proof_x3f___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_dischargeDepth___default;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6___at_Lean_Meta_Simp_recordSimpTheorem___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_config___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Result_dischargeDepth___default;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object*);
extern lean_object* l_Lean_Meta_simpExtension;
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_updateResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_congrCache___default;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_result___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedStep___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_instInhabitedMethods___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_config___default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_usedTheorems___default;
static lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_numSteps___default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_recordSimpTheorem___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_parent_x3f___default;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_State_cache___default;
static lean_object* l_Lean_Meta_Simp_instInhabitedResult___closed__1;
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_Result_proof_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Result_dischargeDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedResult___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_config___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 16);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_config___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_config___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_simpTheorems___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
x_3 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_congrTheorems___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_parent_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_dischargeDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 16);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 4, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 5, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 6, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 7, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 9, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 10, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 11, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 12, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 14, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 15, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_instInhabitedContext___closed__1;
x_3 = l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1;
x_4 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedContext___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Context_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_Context_isDeclToUnfold(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_12 = lean_array_push(x_11, x_6);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Simp_Context_config___default___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2;
x_20 = lean_array_push(x_19, x_6);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_Context_config___default___closed__1;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Context_mkDefault___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Context_mkDefault___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Context_mkDefault(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_cache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Simp_State_cache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_congrCache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Simp_State_congrCache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_usedTheorems___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Meta_Simp_State_usedTheorems___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_State_numSteps___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__2___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__1;
x_2 = l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_instInhabitedResult___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedStep() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedStep___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_result(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_result___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Step_result(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Step_updateResult(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_pre___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Methods_pre___default(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_post___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Methods_post___default(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Methods_discharge_x3f___default___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Methods_discharge_x3f___default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Methods_discharge_x3f___default(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_Simp_instInhabitedStep___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods___closed__1;
x_2 = l_Lean_Meta_Simp_instInhabitedMethods___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedMethods() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_instInhabitedMethods___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_instInhabitedMethods___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedMethods___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_instInhabitedMethods___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_post(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_discharge_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_10, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 3);
lean_dec(x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_4, 3, x_13);
x_14 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_18);
x_21 = lean_apply_8(x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withParent(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withParent___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getSimpTheorems___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpTheorems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getSimpTheorems(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_getSimpCongrTheorems___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimpCongrTheorems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_getSimpCongrTheorems(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_5, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_st_ref_set(x_5, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_4, 1);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_1);
lean_inc(x_5);
x_25 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_5, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
lean_ctor_set(x_29, 0, x_14);
x_33 = lean_st_ref_set(x_5, x_29, x_30);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_26);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 2);
x_40 = lean_ctor_get(x_29, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_st_ref_set(x_5, x_41, x_30);
lean_dec(x_5);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = lean_st_ref_take(x_5, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
lean_ctor_set(x_49, 0, x_14);
x_53 = lean_st_ref_set(x_5, x_49, x_50);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_46);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_49, 1);
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_14);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_st_ref_set(x_5, x_61, x_50);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_4, 0);
x_67 = lean_ctor_get(x_4, 2);
x_68 = lean_ctor_get(x_4, 3);
x_69 = lean_ctor_get(x_4, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_4);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_1);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set(x_70, 4, x_69);
lean_inc(x_5);
x_71 = lean_apply_8(x_2, x_3, x_70, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_st_ref_take(x_5, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 4, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_14);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_79);
x_82 = lean_st_ref_set(x_5, x_81, x_76);
lean_dec(x_5);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_86 = lean_ctor_get(x_71, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
lean_dec(x_71);
x_88 = lean_st_ref_take(x_5, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 3);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 4, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_14);
lean_ctor_set(x_95, 1, x_91);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_93);
x_96 = lean_st_ref_set(x_5, x_95, x_90);
lean_dec(x_5);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get(x_16, 1);
x_101 = lean_ctor_get(x_16, 2);
x_102 = lean_ctor_get(x_16, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_16);
x_103 = l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1;
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
x_105 = lean_st_ref_set(x_5, x_104, x_17);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_4, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 4);
lean_inc(x_110);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_111 = x_4;
} else {
 lean_dec_ref(x_4);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_1);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set(x_112, 3, x_109);
lean_ctor_set(x_112, 4, x_110);
lean_inc(x_5);
x_113 = lean_apply_8(x_2, x_3, x_112, x_5, x_6, x_7, x_8, x_9, x_106);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_st_ref_take(x_5, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_122 = x_117;
} else {
 lean_dec_ref(x_117);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 4, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_14);
lean_ctor_set(x_123, 1, x_119);
lean_ctor_set(x_123, 2, x_120);
lean_ctor_set(x_123, 3, x_121);
x_124 = lean_st_ref_set(x_5, x_123, x_118);
lean_dec(x_5);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_114);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_128 = lean_ctor_get(x_113, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_113, 1);
lean_inc(x_129);
lean_dec(x_113);
x_130 = lean_st_ref_take(x_5, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 3);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 4, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_14);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_134);
lean_ctor_set(x_137, 3, x_135);
x_138 = lean_st_ref_set(x_5, x_137, x_132);
lean_dec(x_5);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
 lean_ctor_set_tag(x_141, 1);
}
lean_ctor_set(x_141, 0, x_128);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_withSimpTheorems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_withSimpTheorems___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Meta_Origin_key(x_4);
x_7 = l_Lean_Meta_Origin_key(x_1);
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
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
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Meta_Origin_key(x_2);
x_6 = l_Lean_Name_hash___override(x_5);
lean_dec(x_5);
x_7 = lean_hashmap_mk_idx(x_4, x_6);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6___at_Lean_Meta_Simp_recordSimpTheorem___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Meta_Origin_key(x_4);
x_8 = l_Lean_Name_hash___override(x_7);
lean_dec(x_7);
x_9 = lean_hashmap_mk_idx(x_6, x_8);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Meta_Origin_key(x_13);
x_18 = l_Lean_Name_hash___override(x_17);
lean_dec(x_17);
x_19 = lean_hashmap_mk_idx(x_16, x_18);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_recordSimpTheorem___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Meta_Simp_recordSimpTheorem___spec__6___at_Lean_Meta_Simp_recordSimpTheorem___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Meta_Simp_recordSimpTheorem___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_Meta_Origin_key(x_6);
x_10 = l_Lean_Meta_Origin_key(x_1);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = l_Lean_Meta_Origin_key(x_13);
x_17 = l_Lean_Meta_Origin_key(x_1);
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_1, x_2, x_15);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Meta_Origin_key(x_2);
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
lean_inc(x_7);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_2, x_11);
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
x_17 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(x_14, x_16);
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
x_20 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Meta_Origin_key(x_2);
x_26 = l_Lean_Name_hash___override(x_25);
lean_dec(x_25);
lean_inc(x_24);
x_27 = lean_hashmap_mk_idx(x_24, x_26);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_2, x_28);
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
x_34 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_HashMapImp_expand___at_Lean_Meta_Simp_recordSimpTheorem___spec__4(x_31, x_33);
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
x_38 = l_Lean_AssocList_replace___at_Lean_Meta_Simp_recordSimpTheorem___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc(x_15);
lean_inc(x_1);
lean_inc(x_14);
x_16 = l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(x_14, x_1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_10, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(x_14, x_1, x_22);
lean_ctor_set(x_10, 2, x_23);
x_24 = lean_st_ref_set(x_3, x_10, x_11);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
x_32 = l_Lean_HashMap_insert___at_Lean_Meta_Simp_recordSimpTheorem___spec__3(x_14, x_1, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_13);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_15);
x_34 = lean_st_ref_set(x_3, x_33, x_11);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_39 = lean_st_ref_set(x_3, x_10, x_11);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Meta_Simp_recordSimpTheorem___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_recordSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_recordSimpTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Result_proof_x3f___default = _init_l_Lean_Meta_Simp_Result_proof_x3f___default();
lean_mark_persistent(l_Lean_Meta_Simp_Result_proof_x3f___default);
l_Lean_Meta_Simp_Result_dischargeDepth___default = _init_l_Lean_Meta_Simp_Result_dischargeDepth___default();
lean_mark_persistent(l_Lean_Meta_Simp_Result_dischargeDepth___default);
l_Lean_Meta_Simp_instInhabitedResult___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult___closed__1);
l_Lean_Meta_Simp_instInhabitedResult___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedResult___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult___closed__2);
l_Lean_Meta_Simp_instInhabitedResult = _init_l_Lean_Meta_Simp_instInhabitedResult();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedResult);
l_Lean_Meta_Simp_Context_config___default___closed__1 = _init_l_Lean_Meta_Simp_Context_config___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_config___default___closed__1);
l_Lean_Meta_Simp_Context_config___default = _init_l_Lean_Meta_Simp_Context_config___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_config___default);
l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1 = _init_l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_simpTheorems___default___closed__1);
l_Lean_Meta_Simp_Context_simpTheorems___default = _init_l_Lean_Meta_Simp_Context_simpTheorems___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_simpTheorems___default);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__1);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__2);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__3);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__4);
l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5 = _init_l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default___closed__5);
l_Lean_Meta_Simp_Context_congrTheorems___default = _init_l_Lean_Meta_Simp_Context_congrTheorems___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_congrTheorems___default);
l_Lean_Meta_Simp_Context_parent_x3f___default = _init_l_Lean_Meta_Simp_Context_parent_x3f___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_parent_x3f___default);
l_Lean_Meta_Simp_Context_dischargeDepth___default = _init_l_Lean_Meta_Simp_Context_dischargeDepth___default();
lean_mark_persistent(l_Lean_Meta_Simp_Context_dischargeDepth___default);
l_Lean_Meta_Simp_instInhabitedContext___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__1);
l_Lean_Meta_Simp_instInhabitedContext___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext___closed__2);
l_Lean_Meta_Simp_instInhabitedContext = _init_l_Lean_Meta_Simp_instInhabitedContext();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedContext);
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__1);
l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2 = _init_l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Context_mkDefault___rarg___closed__2);
l_Lean_Meta_Simp_State_cache___default = _init_l_Lean_Meta_Simp_State_cache___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_cache___default);
l_Lean_Meta_Simp_State_congrCache___default = _init_l_Lean_Meta_Simp_State_congrCache___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_congrCache___default);
l_Lean_Meta_Simp_State_usedTheorems___default = _init_l_Lean_Meta_Simp_State_usedTheorems___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_usedTheorems___default);
l_Lean_Meta_Simp_State_numSteps___default = _init_l_Lean_Meta_Simp_State_numSteps___default();
lean_mark_persistent(l_Lean_Meta_Simp_State_numSteps___default);
l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__1 = _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__1);
l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__2 = _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__2);
l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__3 = _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM___closed__3);
l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM = _init_l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM();
lean_mark_persistent(l_Lean_Meta_Simp_instMonadBacktrackSavedStateSimpM);
l_Lean_Meta_Simp_instInhabitedStep___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedStep___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep___closed__1);
l_Lean_Meta_Simp_instInhabitedStep = _init_l_Lean_Meta_Simp_instInhabitedStep();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedStep);
l_Lean_Meta_Simp_instInhabitedMethods___closed__1 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__1);
l_Lean_Meta_Simp_instInhabitedMethods___closed__2 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__2);
l_Lean_Meta_Simp_instInhabitedMethods___closed__3 = _init_l_Lean_Meta_Simp_instInhabitedMethods___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods___closed__3);
l_Lean_Meta_Simp_instInhabitedMethods = _init_l_Lean_Meta_Simp_instInhabitedMethods();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedMethods);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
