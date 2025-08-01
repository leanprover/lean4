// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.Class Std.Tactic.BVDecide.LRAT.Internal.Assignment Std.Sat.CNF.Basic
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0;
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___boxed(lean_object*, lean_object*);
uint8_t l_Array_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___lam__0(uint8_t, uint8_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_beqDefaultClause____x40_Std_Tactic_BVDecide_LRAT_Internal_Clause___hyg_674____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0(uint8_t, uint8_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_beqAssignment____x40_Std_Tactic_BVDecide_LRAT_Internal_Assignment___hyg_118_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0;
x_3 = 3;
x_4 = lean_box(x_3);
x_5 = lean_mk_array(x_1, x_4);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_array_push(x_2, x_8);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_box(0);
lean_ctor_set(x_1, 1, x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_10;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_array_to_list(x_3);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0;
x_8 = l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(x_6, x_7);
x_9 = lean_array_to_list(x_4);
x_10 = lean_box(0);
x_11 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(x_9, x_10);
x_12 = l_List_appendTR___redArg(x_8, x_11);
x_13 = lean_array_to_list(x_5);
x_14 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(x_13, x_10);
x_15 = l_List_appendTR___redArg(x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
return x_1;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_1, x_8);
x_12 = lean_unbox(x_11);
x_13 = lean_box(0);
x_14 = lean_array_fset(x_1, x_8, x_13);
switch (x_12) {
case 0:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 2;
x_16 = lean_box(x_15);
x_17 = lean_array_fset(x_14, x_8, x_16);
return x_17;
}
case 3:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_array_fset(x_14, x_8, x_19);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(x_12);
x_22 = lean_array_fset(x_14, x_8, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_array_get_size(x_1);
x_25 = lean_nat_dec_lt(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_array_fget(x_1, x_23);
x_27 = lean_unbox(x_26);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_1, x_23, x_28);
switch (x_27) {
case 1:
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 2;
x_31 = lean_box(x_30);
x_32 = lean_array_fset(x_29, x_23, x_31);
return x_32;
}
case 3:
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_array_fset(x_29, x_23, x_34);
return x_35;
}
default: 
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(x_27);
x_37 = lean_array_fset(x_29, x_23, x_36);
return x_37;
}
}
}
}
}
else
{
return x_1;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = 3;
x_8 = lean_box(x_7);
x_9 = lean_mk_array(x_1, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
x_3 = x_9;
goto block_6;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_11, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
x_3 = x_9;
goto block_6;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_16 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(x_2, x_14, x_15, x_9);
x_3 = x_16;
goto block_6;
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_array_push(x_3, x_17);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_16, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_5);
lean_ctor_set(x_21, 3, x_6);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_array_fget(x_6, x_16);
x_23 = lean_unbox(x_22);
x_24 = lean_box(0);
x_25 = lean_array_fset(x_6, x_16, x_24);
switch (x_23) {
case 0:
{
uint8_t x_31; 
x_31 = 2;
x_26 = x_31;
goto block_30;
}
case 3:
{
uint8_t x_32; 
x_32 = 1;
x_26 = x_32;
goto block_30;
}
default: 
{
x_26 = x_23;
goto block_30;
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(x_26);
x_28 = lean_array_fset(x_25, x_16, x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_28);
return x_29;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_2);
x_35 = lean_array_push(x_3, x_34);
x_36 = lean_array_get_size(x_6);
x_37 = lean_nat_dec_lt(x_33, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_5);
lean_ctor_set(x_38, 3, x_6);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_array_fget(x_6, x_33);
x_40 = lean_unbox(x_39);
x_41 = lean_box(0);
x_42 = lean_array_fset(x_6, x_33, x_41);
switch (x_40) {
case 1:
{
uint8_t x_48; 
x_48 = 2;
x_43 = x_48;
goto block_47;
}
case 3:
{
uint8_t x_49; 
x_49 = 0;
x_43 = x_49;
goto block_47;
}
default: 
{
x_43 = x_40;
goto block_47;
}
}
block_47:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_box(x_43);
x_45 = lean_array_fset(x_42, x_33, x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 2, x_5);
lean_ctor_set(x_46, 3, x_45);
return x_46;
}
}
}
}
else
{
lean_dec_ref(x_12);
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_array_push(x_3, x_8);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 4, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_12 = lean_box(0);
x_13 = lean_array_get(x_12, x_3, x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_6);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
if (lean_obj_tag(x_15) == 0)
{
goto block_11;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_array_set(x_3, x_2, x_20);
x_22 = lean_array_get_size(x_6);
x_23 = lean_nat_dec_lt(x_18, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_6);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_array_fget(x_6, x_18);
x_26 = lean_unbox(x_25);
x_27 = lean_box(0);
x_28 = lean_array_fset(x_6, x_18, x_27);
x_29 = lean_unbox(x_19);
lean_dec(x_19);
x_30 = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(x_29, x_26);
x_31 = lean_box(x_30);
x_32 = lean_array_fset(x_28, x_18, x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_4);
lean_ctor_set(x_33, 2, x_5);
lean_ctor_set(x_33, 3, x_32);
return x_33;
}
}
else
{
lean_dec_ref(x_16);
lean_dec_ref(x_15);
goto block_11;
}
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_array_set(x_3, x_2, x_8);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 4, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_array_get(x_11, x_5, x_8);
x_13 = lean_unbox(x_12);
x_14 = lean_unbox(x_9);
x_15 = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(x_14, x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_25; lean_object* x_31; uint8_t x_32; 
lean_dec_ref(x_1);
x_16 = 1;
lean_inc_ref(x_2);
x_17 = lean_array_push(x_4, x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
x_31 = lean_array_get_size(x_5);
x_32 = lean_nat_dec_lt(x_8, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
x_25 = x_5;
goto block_30;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_array_fget(x_5, x_8);
x_34 = lean_unbox(x_33);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_5, x_8, x_35);
x_37 = lean_unbox(x_9);
lean_dec(x_9);
x_38 = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(x_37, x_34);
x_39 = lean_box(x_38);
x_40 = lean_array_fset(x_36, x_8, x_39);
lean_dec(x_8);
x_25 = x_40;
goto block_30;
}
block_24:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_box(x_20);
if (lean_is_scalar(x_18)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_18;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
if (lean_is_scalar(x_7)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_7;
}
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
block_30:
{
uint8_t x_26; 
x_26 = lean_unbox(x_6);
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; 
x_27 = 3;
x_28 = l_Std_Tactic_BVDecide_LRAT_Internal_beqAssignment____x40_Std_Tactic_BVDecide_LRAT_Internal_Assignment___hyg_118_(x_13, x_27);
if (x_28 == 0)
{
lean_dec(x_6);
x_19 = x_25;
x_20 = x_16;
goto block_24;
}
else
{
uint8_t x_29; 
x_29 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = x_25;
x_20 = x_29;
goto block_24;
}
}
else
{
lean_dec(x_6);
x_19 = x_25;
x_20 = x_16;
goto block_24;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 3);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(x_10, x_3);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 3, x_15);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set(x_2, 1, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(x_26, x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(x_9, x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 3, x_14);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set(x_1, 2, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(x_25, x_2);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_unbox(x_7);
x_9 = lean_box(0);
x_10 = lean_array_fset(x_1, x_3, x_9);
x_11 = lean_unbox(x_4);
x_12 = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(x_11, x_8);
x_13 = lean_box(x_12);
x_14 = lean_array_fset(x_10, x_3, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(x_4, x_6);
lean_dec_ref(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_4);
x_8 = x_6;
goto block_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_4);
x_8 = x_6;
goto block_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(x_4, x_16, x_17, x_6);
lean_dec_ref(x_4);
x_8 = x_18;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(0, 4, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_4);
x_7 = x_5;
goto block_10;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_12, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_4);
x_7 = x_5;
goto block_10;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_17 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(x_4, x_15, x_16, x_5);
lean_dec_ref(x_4);
x_7 = x_17;
goto block_10;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
if (lean_is_scalar(x_6)) {
 x_9 = lean_alloc_ctor(0, 4, 0);
} else {
 x_9 = x_6;
}
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_11 = lean_unbox(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_13 = x_3;
} else {
 lean_dec_ref(x_3);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_15 = x_5;
} else {
 lean_dec_ref(x_5);
 x_15 = lean_box(0);
}
x_16 = 1;
x_22 = lean_array_get_size(x_2);
x_23 = lean_nat_dec_lt(x_4, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
goto block_21;
}
else
{
lean_object* x_24; 
x_24 = lean_array_fget(x_2, x_4);
if (lean_obj_tag(x_24) == 0)
{
goto block_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(x_1, x_25, x_12);
switch (lean_obj_tag(x_26)) {
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_array_get(x_31, x_12, x_28);
x_33 = lean_unbox(x_32);
x_34 = lean_unbox(x_29);
x_35 = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_9);
x_44 = lean_array_get_size(x_12);
x_45 = lean_nat_dec_lt(x_28, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
x_36 = x_12;
goto block_43;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_array_fget(x_12, x_28);
x_47 = lean_unbox(x_46);
x_48 = lean_box(0);
x_49 = lean_array_fset(x_12, x_28, x_48);
x_50 = lean_unbox(x_29);
lean_dec(x_29);
x_51 = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(x_50, x_47);
x_52 = lean_box(x_51);
x_53 = lean_array_fset(x_49, x_28, x_52);
lean_dec(x_28);
x_36 = x_53;
goto block_43;
}
}
else
{
uint8_t x_54; 
lean_dec(x_29);
lean_dec(x_28);
x_54 = !lean_is_exclusive(x_27);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_27, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_27, 0);
lean_dec(x_56);
lean_inc(x_9);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 0, x_9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_27);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_27);
lean_inc(x_9);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_9);
lean_ctor_set(x_59, 1, x_9);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_14);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_43:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_14);
x_38 = lean_box(x_35);
x_39 = lean_box(x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 3:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_box(x_16);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_9);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_12);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_26);
x_66 = lean_box(x_16);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_9);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(x_16);
if (lean_is_scalar(x_10)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_10;
}
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
if (lean_is_scalar(x_13)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_13;
}
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_3;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(x_1, x_2, x_6, x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_7);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_8 = x_2;
} else {
 lean_dec_ref(x_2);
 x_8 = lean_box(0);
}
x_14 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_3);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
x_9 = x_7;
x_10 = x_14;
goto block_13;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
x_9 = x_7;
x_10 = x_14;
goto block_13;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_14);
x_20 = 0;
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(x_1, x_4, x_3, x_20, x_21, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_9 = x_23;
x_10 = x_24;
goto block_13;
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
if (lean_is_scalar(x_8)) {
 x_11 = lean_alloc_ctor(0, 4, 0);
} else {
 x_11 = x_8;
}
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_6 = x_1;
} else {
 lean_dec_ref(x_1);
 x_6 = lean_box(0);
}
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 1);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_4, 1, x_16);
x_7 = x_4;
goto block_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_7 = x_20;
goto block_10;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_4, 1, x_24);
x_7 = x_4;
goto block_10;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_7 = x_28;
goto block_10;
}
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_box(0);
lean_inc(x_3);
x_6 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(x_3, x_5);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(x_1, x_2, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = 1;
x_12 = lean_unbox(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_7);
x_13 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_9, x_4);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = lean_unbox(x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_3);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec_ref(x_13);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec_ref(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 3);
x_27 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_26, x_24);
lean_dec(x_24);
lean_ctor_set(x_23, 3, x_27);
x_28 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_23);
x_29 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_28, x_3);
x_30 = lean_box(x_11);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_35 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_34, x_24);
lean_dec(x_24);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_36);
x_38 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_37, x_3);
x_39 = lean_box(x_11);
lean_ctor_set(x_15, 1, x_39);
lean_ctor_set(x_15, 0, x_38);
return x_15;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_14);
lean_dec(x_3);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_42);
lean_dec_ref(x_13);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_16);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
lean_dec_ref(x_13);
x_45 = lean_ctor_get(x_14, 0);
lean_inc(x_45);
lean_dec(x_14);
x_46 = lean_ctor_get(x_44, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_44, 3);
lean_inc_ref(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
x_51 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_49, x_45);
lean_dec(x_45);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_51);
x_53 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_52);
x_54 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_53, x_3);
x_55 = lean_box(x_11);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_15, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_15, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_13, 0);
lean_inc(x_60);
lean_dec_ref(x_13);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 0, x_60);
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_15);
x_61 = lean_ctor_get(x_13, 0);
lean_inc(x_61);
lean_dec_ref(x_13);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_10);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
x_63 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_9);
x_64 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_63, x_3);
x_65 = lean_box(x_11);
lean_ctor_set(x_7, 1, x_65);
lean_ctor_set(x_7, 0, x_64);
return x_7;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_68 = 1;
x_69 = lean_unbox(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_66, x_4);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_67);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_unbox(x_75);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_71);
lean_dec(x_3);
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec_ref(x_70);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_73);
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
lean_dec_ref(x_70);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_80, 3);
lean_inc_ref(x_85);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 x_86 = x_80;
} else {
 lean_dec_ref(x_80);
 x_86 = lean_box(0);
}
x_87 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_85, x_81);
lean_dec(x_81);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 4, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_83);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set(x_88, 3, x_87);
x_89 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_88);
x_90 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_89, x_3);
x_91 = lean_box(x_68);
if (lean_is_scalar(x_76)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_76;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_3);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_93 = x_72;
} else {
 lean_dec_ref(x_72);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_70, 0);
lean_inc(x_94);
lean_dec_ref(x_70);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_67);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_67);
x_96 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_66);
x_97 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_96, x_3);
x_98 = lean_box(x_68);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_6, x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_5, x_6);
lean_inc(x_1);
x_16 = lean_array_get(x_1, x_2, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_15);
x_9 = x_8;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___lam__0___boxed), 2, 0);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(x_19, 0, x_3);
x_20 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_21, 0, x_18);
x_22 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_inc_ref(x_4);
x_23 = l_List_elem___redArg(x_22, x_4, x_17);
if (x_23 == 0)
{
lean_dec(x_15);
x_9 = x_8;
goto block_13;
}
else
{
lean_object* x_24; 
x_24 = lean_array_push(x_8, x_15);
x_9 = x_24;
goto block_13;
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_6, x_10);
x_6 = x_11;
x_8 = x_9;
goto _start;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_19; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_box(0);
x_19 = lean_unbox(x_5);
lean_dec(x_5);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_3, 1, x_21);
x_7 = x_3;
goto block_18;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_3, 1, x_23);
x_7 = x_3;
goto block_18;
}
block_18:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_get_size(x_2);
x_9 = l_Array_range(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0;
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_1);
return x_12;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(x_6, x_2, x_1, x_7, x_9, x_15, x_16, x_12);
lean_dec_ref(x_9);
return x_17;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_39; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_box(0);
x_39 = lean_unbox(x_25);
lean_dec(x_25);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 1;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_41);
x_27 = x_42;
goto block_38;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_44);
x_27 = x_45;
goto block_38;
}
block_38:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_array_get_size(x_2);
x_29 = l_Array_range(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0;
x_33 = lean_nat_dec_lt(x_30, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec_ref(x_27);
lean_dec(x_1);
return x_32;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec_ref(x_27);
lean_dec(x_1);
return x_32;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_37 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(x_26, x_2, x_1, x_27, x_29, x_35, x_36, x_32);
lean_dec_ref(x_29);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(x_1, x_5, x_3);
x_7 = lean_array_size(x_4);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(x_7, x_8, x_4);
x_10 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_11 = l_Array_instDecidableEq___redArg(x_10, x_6, x_9);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_box(0);
x_11 = lean_array_get(x_10, x_7, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_4);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0___boxed), 2, 0);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
lean_inc(x_14);
x_21 = l_List_eraseTR_go___redArg(x_19, x_14, x_3, x_14, x_20);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(x_21, x_22);
x_24 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(x_2, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = 1;
x_29 = lean_unbox(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_free_object(x_24);
x_30 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_26, x_9);
lean_dec(x_9);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_ctor_get(x_33, 3);
x_40 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_39, x_34);
lean_dec(x_34);
lean_ctor_set(x_33, 3, x_40);
x_41 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_33);
x_42 = lean_unbox(x_38);
lean_dec(x_38);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_unbox(x_37);
lean_dec(x_37);
if (x_43 == 0)
{
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
else
{
lean_object* x_44; 
lean_dec(x_27);
x_44 = lean_box(x_28);
lean_ctor_set(x_32, 1, x_44);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
}
else
{
lean_dec(x_37);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
x_49 = lean_ctor_get(x_33, 2);
x_50 = lean_ctor_get(x_33, 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_51 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_50, x_34);
lean_dec(x_34);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_51);
x_53 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_52);
x_54 = lean_unbox(x_46);
lean_dec(x_46);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_unbox(x_45);
lean_dec(x_45);
if (x_55 == 0)
{
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 0, x_53);
return x_32;
}
else
{
lean_object* x_56; 
lean_dec(x_27);
x_56 = lean_box(x_28);
lean_ctor_set(x_32, 1, x_56);
lean_ctor_set(x_32, 0, x_53);
return x_32;
}
}
else
{
lean_dec(x_45);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 0, x_53);
return x_32;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_57 = lean_ctor_get(x_32, 0);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_32);
x_59 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_33, 3);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_63 = x_33;
} else {
 lean_dec_ref(x_33);
 x_63 = lean_box(0);
}
x_64 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_62, x_34);
lean_dec(x_34);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 4, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_64);
x_66 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_65);
x_67 = lean_unbox(x_58);
lean_dec(x_58);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = lean_unbox(x_57);
lean_dec(x_57);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_27);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_27);
x_70 = lean_box(x_28);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_57);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_27);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_1);
x_73 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_26);
x_74 = lean_box(x_28);
lean_ctor_set(x_24, 1, x_74);
lean_ctor_set(x_24, 0, x_73);
return x_24;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_24, 0);
x_76 = lean_ctor_get(x_24, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_24);
x_77 = 1;
x_78 = lean_unbox(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_79 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_75, x_9);
lean_dec(x_9);
lean_dec(x_1);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec_ref(x_79);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_82, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_82, 2);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_82, 3);
lean_inc_ref(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
x_92 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_90, x_83);
lean_dec(x_83);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_93);
x_95 = lean_unbox(x_85);
lean_dec(x_85);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_unbox(x_84);
lean_dec(x_84);
if (x_96 == 0)
{
lean_object* x_97; 
if (lean_is_scalar(x_86)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_86;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_76);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_76);
x_98 = lean_box(x_77);
if (lean_is_scalar(x_86)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_86;
}
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_84);
if (lean_is_scalar(x_86)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_86;
}
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_76);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_76);
lean_dec(x_9);
lean_dec(x_1);
x_101 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_75);
x_102 = lean_box(x_77);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_2, 0);
x_105 = lean_ctor_get(x_4, 0);
x_106 = lean_ctor_get(x_4, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_4);
x_107 = lean_box(0);
x_108 = lean_array_get(x_107, x_104, x_105);
lean_dec(x_105);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_106);
lean_dec_ref(x_3);
lean_dec(x_1);
x_109 = 0;
x_110 = lean_box(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; 
x_112 = lean_ctor_get(x_108, 0);
lean_inc(x_112);
lean_dec_ref(x_108);
x_113 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0___boxed), 2, 0);
lean_inc(x_1);
x_114 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(x_114, 0, x_1);
x_115 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_115, 0, x_114);
x_116 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_116, 0, x_113);
x_117 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
lean_inc(x_112);
x_119 = l_List_eraseTR_go___redArg(x_117, x_112, x_3, x_112, x_118);
lean_dec(x_112);
x_120 = lean_box(0);
x_121 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(x_119, x_120);
x_122 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(x_2, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = 1;
x_127 = lean_unbox(x_124);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_125);
x_128 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_123, x_106);
lean_dec(x_106);
lean_dec(x_1);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec_ref(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_131, 1);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_131, 2);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_131, 3);
lean_inc_ref(x_139);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_140 = x_131;
} else {
 lean_dec_ref(x_131);
 x_140 = lean_box(0);
}
x_141 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_139, x_132);
lean_dec(x_132);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 4, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_137);
lean_ctor_set(x_142, 2, x_138);
lean_ctor_set(x_142, 3, x_141);
x_143 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_142);
x_144 = lean_unbox(x_134);
lean_dec(x_134);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = lean_unbox(x_133);
lean_dec(x_133);
if (x_145 == 0)
{
lean_object* x_146; 
if (lean_is_scalar(x_135)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_135;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_124);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_124);
x_147 = lean_box(x_126);
if (lean_is_scalar(x_135)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_135;
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_dec(x_133);
if (lean_is_scalar(x_135)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_135;
}
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_124);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_124);
lean_dec(x_106);
lean_dec(x_1);
x_150 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_123);
x_151 = lean_box(x_126);
if (lean_is_scalar(x_125)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_125;
}
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_153 = lean_ctor_get(x_2, 0);
x_154 = lean_ctor_get(x_2, 1);
x_155 = lean_ctor_get(x_2, 2);
x_156 = lean_ctor_get(x_2, 3);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_2);
x_157 = lean_ctor_get(x_4, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_159 = x_4;
} else {
 lean_dec_ref(x_4);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
x_161 = lean_array_get(x_160, x_153, x_157);
lean_dec(x_157);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
lean_dec_ref(x_3);
lean_dec(x_1);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_155);
lean_ctor_set(x_162, 3, x_156);
x_163 = 0;
x_164 = lean_box(x_163);
if (lean_is_scalar(x_159)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_159;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; 
lean_dec(x_159);
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
lean_dec_ref(x_161);
x_167 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0___boxed), 2, 0);
lean_inc(x_1);
x_168 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(x_168, 0, x_1);
x_169 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_169, 0, x_168);
x_170 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_170, 0, x_167);
x_171 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_171, 0, x_169);
lean_closure_set(x_171, 1, x_170);
x_172 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
lean_inc(x_166);
x_173 = l_List_eraseTR_go___redArg(x_171, x_166, x_3, x_166, x_172);
lean_dec(x_166);
x_174 = lean_box(0);
x_175 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(x_173, x_174);
x_176 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_176, 0, x_153);
lean_ctor_set(x_176, 1, x_154);
lean_ctor_set(x_176, 2, x_155);
lean_ctor_set(x_176, 3, x_156);
x_177 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(x_176, x_175);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
x_181 = 1;
x_182 = lean_unbox(x_179);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_180);
x_183 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_178, x_158);
lean_dec(x_158);
lean_dec(x_1);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec_ref(x_183);
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
lean_dec(x_184);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_190 = x_185;
} else {
 lean_dec_ref(x_185);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_186, 0);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_186, 1);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_186, 2);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_186, 3);
lean_inc_ref(x_194);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 x_195 = x_186;
} else {
 lean_dec_ref(x_186);
 x_195 = lean_box(0);
}
x_196 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_194, x_187);
lean_dec(x_187);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 4, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_191);
lean_ctor_set(x_197, 1, x_192);
lean_ctor_set(x_197, 2, x_193);
lean_ctor_set(x_197, 3, x_196);
x_198 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_197);
x_199 = lean_unbox(x_189);
lean_dec(x_189);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = lean_unbox(x_188);
lean_dec(x_188);
if (x_200 == 0)
{
lean_object* x_201; 
if (lean_is_scalar(x_190)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_190;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_179);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_179);
x_202 = lean_box(x_181);
if (lean_is_scalar(x_190)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_190;
}
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_188);
if (lean_is_scalar(x_190)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_190;
}
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_179);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_179);
lean_dec(x_158);
lean_dec(x_1);
x_205 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(x_178);
x_206 = lean_box(x_181);
if (lean_is_scalar(x_180)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_180;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 1);
lean_dec(x_15);
x_16 = lean_box(x_1);
lean_ctor_set(x_5, 1, x_16);
x_8 = x_5;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_8 = x_19;
goto block_11;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 1);
lean_dec(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_5, 1, x_23);
x_8 = x_5;
goto block_11;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_8 = x_27;
goto block_11;
}
}
block_11:
{
lean_object* x_9; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(1, 2, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_2 = x_6;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
x_8 = x_7;
goto block_12;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_array_uget(x_4, x_5);
x_22 = lean_unbox(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_19);
lean_ctor_set(x_7, 0, x_19);
lean_inc(x_2);
x_23 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(x_2, x_17, x_7, x_21);
x_8 = x_23;
goto block_12;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_24 = lean_box(x_3);
lean_inc(x_19);
lean_ctor_set(x_7, 1, x_24);
lean_ctor_set(x_7, 0, x_19);
lean_inc(x_2);
x_25 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(x_2, x_17, x_7, x_21);
x_8 = x_25;
goto block_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_array_uget(x_4, x_5);
x_30 = lean_unbox(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_14);
lean_inc(x_2);
x_32 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(x_2, x_26, x_31, x_29);
x_8 = x_32;
goto block_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_33 = lean_box(x_3);
lean_inc(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_2);
x_35 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(x_2, x_26, x_34, x_29);
x_8 = x_35;
goto block_12;
}
}
}
}
else
{
lean_dec(x_2);
return x_7;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_5, x_9);
x_5 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_1);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(x_1, x_2, x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_box(0);
lean_inc(x_3);
x_11 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(x_7, x_3, x_10);
x_12 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(x_1, x_2, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(x_1, x_15, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_49; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_44 = x_21;
} else {
 lean_dec_ref(x_21);
 x_44 = lean_box(0);
}
x_49 = lean_unbox(x_43);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_13);
x_50 = lean_unbox(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_43);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_6);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
lean_dec(x_52);
lean_free_object(x_16);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_45 = x_19;
x_46 = x_7;
goto block_48;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_52, x_52);
if (x_54 == 0)
{
lean_dec(x_52);
lean_free_object(x_16);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_45 = x_19;
x_46 = x_7;
goto block_48;
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_box(x_7);
lean_ctor_set(x_16, 1, x_55);
x_56 = 0;
x_57 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_58 = lean_unbox(x_42);
lean_inc(x_1);
x_59 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(x_4, x_1, x_58, x_6, x_56, x_57, x_16);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
x_45 = x_60;
x_46 = x_62;
goto block_48;
}
}
}
else
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_16, 1, x_43);
return x_16;
}
}
else
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_41:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_23, 3);
x_26 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_25, x_20);
lean_dec(x_20);
lean_ctor_set(x_23, 3, x_26);
x_27 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_23);
lean_dec(x_1);
x_28 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_27, x_3);
x_29 = lean_box(x_7);
if (lean_is_scalar(x_22)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_22;
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_35 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_34, x_20);
lean_dec(x_20);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_36);
lean_dec(x_1);
x_38 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_37, x_3);
x_39 = lean_box(x_7);
if (lean_is_scalar(x_22)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_22;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
block_48:
{
if (x_46 == 0)
{
if (x_7 == 0)
{
lean_dec(x_44);
lean_dec(x_42);
x_23 = x_45;
goto block_41;
}
else
{
lean_object* x_47; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
else
{
lean_dec(x_44);
lean_dec(x_42);
x_23 = x_45;
goto block_41;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_88; 
x_63 = lean_ctor_get(x_16, 1);
x_64 = lean_ctor_get(x_16, 0);
lean_inc(x_63);
lean_inc(x_64);
lean_dec(x_16);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_81 = lean_ctor_get(x_66, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_83 = x_66;
} else {
 lean_dec_ref(x_66);
 x_83 = lean_box(0);
}
x_88 = lean_unbox(x_82);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_13);
x_89 = lean_unbox(x_81);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_82);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_array_get_size(x_6);
x_92 = lean_nat_dec_lt(x_90, x_91);
if (x_92 == 0)
{
lean_dec(x_91);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_84 = x_64;
x_85 = x_7;
goto block_87;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_91, x_91);
if (x_93 == 0)
{
lean_dec(x_91);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_84 = x_64;
x_85 = x_7;
goto block_87;
}
else
{
lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_94 = lean_box(x_7);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_64);
lean_ctor_set(x_95, 1, x_94);
x_96 = 0;
x_97 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_98 = lean_unbox(x_81);
lean_inc(x_1);
x_99 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(x_4, x_1, x_98, x_6, x_96, x_97, x_95);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
x_84 = x_100;
x_85 = x_102;
goto block_87;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_67);
lean_dec(x_65);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_64);
lean_ctor_set(x_103, 1, x_82);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_67);
lean_dec(x_65);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_64);
lean_ctor_set(x_104, 1, x_13);
return x_104;
}
block_80:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_68, 2);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_68, 3);
lean_inc_ref(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = l_List_foldl___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(x_72, x_65);
lean_dec(x_65);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 4, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_74);
x_76 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(x_1, x_75);
lean_dec(x_1);
x_77 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(x_76, x_3);
x_78 = lean_box(x_7);
if (lean_is_scalar(x_67)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_67;
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
block_87:
{
if (x_85 == 0)
{
if (x_7 == 0)
{
lean_dec(x_83);
lean_dec(x_81);
x_68 = x_84;
goto block_80;
}
else
{
lean_object* x_86; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_81);
return x_86;
}
}
else
{
lean_dec(x_83);
lean_dec(x_81);
x_68 = x_84;
goto block_80;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_13);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_12);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_12, 1);
lean_dec(x_106);
x_107 = 0;
x_108 = lean_box(x_107);
lean_ctor_set(x_12, 1, x_108);
return x_12;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_12, 0);
lean_inc(x_109);
lean_dec(x_12);
x_110 = 0;
x_111 = lean_box(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(x_1, x_2, x_8, x_4, x_9, x_10, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_apply_2(x_1, x_7, x_8);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = lean_box(0);
lean_inc_ref(x_1);
x_14 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0(x_1, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_6 = x_16;
goto block_10;
}
else
{
x_6 = x_5;
goto block_10;
}
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_4, x_7);
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_4);
x_13 = lean_box(0);
lean_inc_ref(x_1);
x_14 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0(x_1, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_6 = x_16;
goto block_10;
}
else
{
x_6 = x_5;
goto block_10;
}
}
block_10:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_4, x_7);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__1(x_1, x_2, x_3, x_8, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_beqDefaultClause____x40_Std_Tactic_BVDecide_LRAT_Internal_Clause___hyg_674____boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_array_size(x_3);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(x_5, x_3, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Assignment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1);
l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
