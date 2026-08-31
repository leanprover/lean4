// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_range(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(uint8_t, uint8_t);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(uint8_t, uint8_t);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(uint8_t, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(uint8_t, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited(lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0));
v___x_5_ = 3;
v___x_6_ = lean_box(v___x_5_);
v___x_7_ = lean_mk_array(v_n_3_, v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_8_, 0, v___x_4_);
lean_ctor_set(v___x_8_, 1, v___x_4_);
lean_ctor_set(v___x_8_, 2, v___x_4_);
lean_ctor_set(v___x_8_, 3, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
if (lean_obj_tag(v_a_9_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = l_List_reverse___redArg(v_a_10_);
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_head_12_ = lean_ctor_get(v_a_9_, 0);
v_tail_13_ = lean_ctor_get(v_a_9_, 1);
v_isSharedCheck_23_ = !lean_is_exclusive(v_a_9_);
if (v_isSharedCheck_23_ == 0)
{
v___x_15_ = v_a_9_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_tail_13_);
lean_inc(v_head_12_);
lean_dec(v_a_9_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_17_ = lean_box(0);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v___x_17_);
v___x_19_ = v___x_15_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_head_12_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v___x_17_);
v___x_19_ = v_reuseFailAlloc_22_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; 
v___x_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v_a_10_);
v_a_9_ = v_tail_13_;
v_a_10_ = v___x_20_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
if (lean_obj_tag(v_a_24_) == 0)
{
lean_object* v___x_26_; 
v___x_26_ = lean_array_to_list(v_a_25_);
return v___x_26_;
}
else
{
lean_object* v_head_27_; 
v_head_27_ = lean_ctor_get(v_a_24_, 0);
if (lean_obj_tag(v_head_27_) == 0)
{
lean_object* v_tail_28_; 
v_tail_28_ = lean_ctor_get(v_a_24_, 1);
lean_inc(v_tail_28_);
lean_dec_ref_known(v_a_24_, 2);
v_a_24_ = v_tail_28_;
goto _start;
}
else
{
lean_object* v_tail_30_; lean_object* v_val_31_; lean_object* v___x_32_; 
lean_inc_ref(v_head_27_);
v_tail_30_ = lean_ctor_get(v_a_24_, 1);
lean_inc(v_tail_30_);
lean_dec_ref_known(v_a_24_, 2);
v_val_31_ = lean_ctor_get(v_head_27_, 0);
lean_inc(v_val_31_);
lean_dec_ref_known(v_head_27_, 1);
v___x_32_ = lean_array_push(v_a_25_, v_val_31_);
v_a_24_ = v_tail_30_;
v_a_25_ = v___x_32_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(lean_object* v_n_36_, lean_object* v_f_37_){
_start:
{
lean_object* v_clauses_38_; lean_object* v_rupUnits_39_; lean_object* v_ratUnits_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_clauses_38_ = lean_ctor_get(v_f_37_, 0);
lean_inc_ref(v_clauses_38_);
v_rupUnits_39_ = lean_ctor_get(v_f_37_, 1);
lean_inc_ref(v_rupUnits_39_);
v_ratUnits_40_ = lean_ctor_get(v_f_37_, 2);
lean_inc_ref(v_ratUnits_40_);
lean_dec_ref(v_f_37_);
v___x_41_ = lean_array_to_list(v_clauses_38_);
v___x_42_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0));
v___x_43_ = l_List_filterMapTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(v___x_41_, v___x_42_);
v___x_44_ = lean_array_to_list(v_rupUnits_39_);
v___x_45_ = lean_box(0);
v___x_46_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(v___x_44_, v___x_45_);
v___x_47_ = l_List_appendTR___redArg(v___x_43_, v___x_46_);
v___x_48_ = lean_array_to_list(v_ratUnits_40_);
v___x_49_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(v___x_48_, v___x_45_);
v___x_50_ = l_List_appendTR___redArg(v___x_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed(lean_object* v_n_51_, lean_object* v_f_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(v_n_51_, v_f_52_);
lean_dec(v_n_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(lean_object* v_n_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(v_a_55_, v_a_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___boxed(lean_object* v_n_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(v_n_58_, v_a_59_, v_a_60_);
lean_dec(v_n_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(lean_object* v_assignments_62_, lean_object* v_cOpt_63_){
_start:
{
if (lean_obj_tag(v_cOpt_63_) == 0)
{
return v_assignments_62_;
}
else
{
lean_object* v_val_64_; 
v_val_64_ = lean_ctor_get(v_cOpt_63_, 0);
if (lean_obj_tag(v_val_64_) == 1)
{
lean_object* v_tail_65_; 
v_tail_65_ = lean_ctor_get(v_val_64_, 1);
if (lean_obj_tag(v_tail_65_) == 0)
{
lean_object* v_head_66_; lean_object* v_snd_67_; uint8_t v___x_68_; 
v_head_66_ = lean_ctor_get(v_val_64_, 0);
v_snd_67_ = lean_ctor_get(v_head_66_, 1);
v___x_68_ = lean_unbox(v_snd_67_);
if (v___x_68_ == 0)
{
lean_object* v_fst_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_fst_69_ = lean_ctor_get(v_head_66_, 0);
v___x_70_ = lean_array_get_size(v_assignments_62_);
v___x_71_ = lean_nat_dec_lt(v_fst_69_, v___x_70_);
if (v___x_71_ == 0)
{
return v_assignments_62_;
}
else
{
lean_object* v_v_72_; lean_object* v___x_73_; lean_object* v_xs_x27_74_; uint8_t v___x_75_; 
v_v_72_ = lean_array_fget(v_assignments_62_, v_fst_69_);
v___x_73_ = lean_box(0);
v_xs_x27_74_ = lean_array_fset(v_assignments_62_, v_fst_69_, v___x_73_);
v___x_75_ = lean_unbox(v_v_72_);
switch(v___x_75_)
{
case 0:
{
uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_v_72_);
v___x_76_ = 2;
v___x_77_ = lean_box(v___x_76_);
v___x_78_ = lean_array_fset(v_xs_x27_74_, v_fst_69_, v___x_77_);
return v___x_78_;
}
case 3:
{
uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_v_72_);
v___x_79_ = 1;
v___x_80_ = lean_box(v___x_79_);
v___x_81_ = lean_array_fset(v_xs_x27_74_, v_fst_69_, v___x_80_);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; 
v___x_82_ = lean_array_fset(v_xs_x27_74_, v_fst_69_, v_v_72_);
return v___x_82_;
}
}
}
}
else
{
lean_object* v_fst_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_fst_83_ = lean_ctor_get(v_head_66_, 0);
v___x_84_ = lean_array_get_size(v_assignments_62_);
v___x_85_ = lean_nat_dec_lt(v_fst_83_, v___x_84_);
if (v___x_85_ == 0)
{
return v_assignments_62_;
}
else
{
lean_object* v_v_86_; lean_object* v___x_87_; lean_object* v_xs_x27_88_; uint8_t v___x_89_; 
v_v_86_ = lean_array_fget(v_assignments_62_, v_fst_83_);
v___x_87_ = lean_box(0);
v_xs_x27_88_ = lean_array_fset(v_assignments_62_, v_fst_83_, v___x_87_);
v___x_89_ = lean_unbox(v_v_86_);
switch(v___x_89_)
{
case 1:
{
uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_v_86_);
v___x_90_ = 2;
v___x_91_ = lean_box(v___x_90_);
v___x_92_ = lean_array_fset(v_xs_x27_88_, v_fst_83_, v___x_91_);
return v___x_92_;
}
case 3:
{
uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_v_86_);
v___x_93_ = 0;
v___x_94_ = lean_box(v___x_93_);
v___x_95_ = lean_array_fset(v_xs_x27_88_, v_fst_83_, v___x_94_);
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; 
v___x_96_ = lean_array_fset(v_xs_x27_88_, v_fst_83_, v_v_86_);
return v___x_96_;
}
}
}
}
}
else
{
return v_assignments_62_;
}
}
else
{
return v_assignments_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg___boxed(lean_object* v_assignments_97_, lean_object* v_cOpt_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(v_assignments_97_, v_cOpt_98_);
lean_dec(v_cOpt_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(lean_object* v_n_100_, lean_object* v_assignments_101_, lean_object* v_cOpt_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(v_assignments_101_, v_cOpt_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___boxed(lean_object* v_n_104_, lean_object* v_assignments_105_, lean_object* v_cOpt_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(v_n_104_, v_assignments_105_, v_cOpt_106_);
lean_dec(v_cOpt_106_);
lean_dec(v_n_104_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(lean_object* v_as_108_, size_t v_i_109_, size_t v_stop_110_, lean_object* v_b_111_){
_start:
{
uint8_t v___x_112_; 
v___x_112_ = lean_usize_dec_eq(v_i_109_, v_stop_110_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; size_t v___x_115_; size_t v___x_116_; 
v___x_113_ = lean_array_uget_borrowed(v_as_108_, v_i_109_);
v___x_114_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(v_b_111_, v___x_113_);
v___x_115_ = ((size_t)1ULL);
v___x_116_ = lean_usize_add(v_i_109_, v___x_115_);
v_i_109_ = v___x_116_;
v_b_111_ = v___x_114_;
goto _start;
}
else
{
return v_b_111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg___boxed(lean_object* v_as_118_, lean_object* v_i_119_, lean_object* v_stop_120_, lean_object* v_b_121_){
_start:
{
size_t v_i_boxed_122_; size_t v_stop_boxed_123_; lean_object* v_res_124_; 
v_i_boxed_122_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_stop_boxed_123_ = lean_unbox_usize(v_stop_120_);
lean_dec(v_stop_120_);
v_res_124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_as_118_, v_i_boxed_122_, v_stop_boxed_123_, v_b_121_);
lean_dec_ref(v_as_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object* v_n_127_, lean_object* v_clauses_128_){
_start:
{
lean_object* v___y_130_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_133_ = 3;
v___x_134_ = lean_box(v___x_133_);
v___x_135_ = lean_mk_array(v_n_127_, v___x_134_);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_array_get_size(v_clauses_128_);
v___x_138_ = lean_nat_dec_lt(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
v___y_130_ = v___x_135_;
goto v___jp_129_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = lean_nat_dec_le(v___x_137_, v___x_137_);
if (v___x_139_ == 0)
{
if (v___x_138_ == 0)
{
v___y_130_ = v___x_135_;
goto v___jp_129_;
}
else
{
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_137_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_clauses_128_, v___x_140_, v___x_141_, v___x_135_);
v___y_130_ = v___x_142_;
goto v___jp_129_;
}
}
else
{
size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v___x_143_ = ((size_t)0ULL);
v___x_144_ = lean_usize_of_nat(v___x_137_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_clauses_128_, v___x_143_, v___x_144_, v___x_135_);
v___y_130_ = v___x_145_;
goto v___jp_129_;
}
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
v___x_132_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_132_, 0, v_clauses_128_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_ctor_set(v___x_132_, 2, v___x_131_);
lean_ctor_set(v___x_132_, 3, v___y_130_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(lean_object* v_n_146_, lean_object* v_as_147_, size_t v_i_148_, size_t v_stop_149_, lean_object* v_b_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_as_147_, v_i_148_, v_stop_149_, v_b_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___boxed(lean_object* v_n_152_, lean_object* v_as_153_, lean_object* v_i_154_, lean_object* v_stop_155_, lean_object* v_b_156_){
_start:
{
size_t v_i_boxed_157_; size_t v_stop_boxed_158_; lean_object* v_res_159_; 
v_i_boxed_157_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_stop_boxed_158_ = lean_unbox_usize(v_stop_155_);
lean_dec(v_stop_155_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(v_n_152_, v_as_153_, v_i_boxed_157_, v_stop_boxed_158_, v_b_156_);
lean_dec_ref(v_as_153_);
lean_dec(v_n_152_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(lean_object* v_f_160_, lean_object* v_c_161_){
_start:
{
lean_object* v_clauses_162_; lean_object* v_rupUnits_163_; lean_object* v_ratUnits_164_; lean_object* v_assignments_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_215_; 
v_clauses_162_ = lean_ctor_get(v_f_160_, 0);
v_rupUnits_163_ = lean_ctor_get(v_f_160_, 1);
v_ratUnits_164_ = lean_ctor_get(v_f_160_, 2);
v_assignments_165_ = lean_ctor_get(v_f_160_, 3);
v_isSharedCheck_215_ = !lean_is_exclusive(v_f_160_);
if (v_isSharedCheck_215_ == 0)
{
v___x_167_ = v_f_160_;
v_isShared_168_ = v_isSharedCheck_215_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_assignments_165_);
lean_inc(v_ratUnits_164_);
lean_inc(v_rupUnits_163_);
lean_inc(v_clauses_162_);
lean_dec(v_f_160_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_215_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
if (lean_obj_tag(v_c_161_) == 1)
{
lean_object* v_tail_175_; 
v_tail_175_ = lean_ctor_get(v_c_161_, 1);
if (lean_obj_tag(v_tail_175_) == 0)
{
lean_object* v_head_176_; lean_object* v_snd_177_; uint8_t v___x_178_; 
lean_del_object(v___x_167_);
v_head_176_ = lean_ctor_get(v_c_161_, 0);
v_snd_177_ = lean_ctor_get(v_head_176_, 1);
v___x_178_ = lean_unbox(v_snd_177_);
if (v___x_178_ == 0)
{
lean_object* v_fst_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_fst_179_ = lean_ctor_get(v_head_176_, 0);
lean_inc(v_fst_179_);
v___x_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_180_, 0, v_c_161_);
v___x_181_ = lean_array_push(v_clauses_162_, v___x_180_);
v___x_182_ = lean_array_get_size(v_assignments_165_);
v___x_183_ = lean_nat_dec_lt(v_fst_179_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec(v_fst_179_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v_rupUnits_163_);
lean_ctor_set(v___x_184_, 2, v_ratUnits_164_);
lean_ctor_set(v___x_184_, 3, v_assignments_165_);
return v___x_184_;
}
else
{
lean_object* v_v_185_; lean_object* v___x_186_; lean_object* v_xs_x27_187_; uint8_t v___y_189_; uint8_t v___x_193_; 
v_v_185_ = lean_array_fget(v_assignments_165_, v_fst_179_);
v___x_186_ = lean_box(0);
v_xs_x27_187_ = lean_array_fset(v_assignments_165_, v_fst_179_, v___x_186_);
v___x_193_ = lean_unbox(v_v_185_);
switch(v___x_193_)
{
case 0:
{
uint8_t v___x_194_; 
lean_dec(v_v_185_);
v___x_194_ = 2;
v___y_189_ = v___x_194_;
goto v___jp_188_;
}
case 3:
{
uint8_t v___x_195_; 
lean_dec(v_v_185_);
v___x_195_ = 1;
v___y_189_ = v___x_195_;
goto v___jp_188_;
}
default: 
{
uint8_t v___x_196_; 
v___x_196_ = lean_unbox(v_v_185_);
lean_dec(v_v_185_);
v___y_189_ = v___x_196_;
goto v___jp_188_;
}
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_box(v___y_189_);
v___x_191_ = lean_array_fset(v_xs_x27_187_, v_fst_179_, v___x_190_);
lean_dec(v_fst_179_);
v___x_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_192_, 0, v___x_181_);
lean_ctor_set(v___x_192_, 1, v_rupUnits_163_);
lean_ctor_set(v___x_192_, 2, v_ratUnits_164_);
lean_ctor_set(v___x_192_, 3, v___x_191_);
return v___x_192_;
}
}
}
else
{
lean_object* v_fst_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_fst_197_ = lean_ctor_get(v_head_176_, 0);
lean_inc(v_fst_197_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v_c_161_);
v___x_199_ = lean_array_push(v_clauses_162_, v___x_198_);
v___x_200_ = lean_array_get_size(v_assignments_165_);
v___x_201_ = lean_nat_dec_lt(v_fst_197_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
lean_dec(v_fst_197_);
v___x_202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_202_, 0, v___x_199_);
lean_ctor_set(v___x_202_, 1, v_rupUnits_163_);
lean_ctor_set(v___x_202_, 2, v_ratUnits_164_);
lean_ctor_set(v___x_202_, 3, v_assignments_165_);
return v___x_202_;
}
else
{
lean_object* v_v_203_; lean_object* v___x_204_; lean_object* v_xs_x27_205_; uint8_t v___y_207_; uint8_t v___x_211_; 
v_v_203_ = lean_array_fget(v_assignments_165_, v_fst_197_);
v___x_204_ = lean_box(0);
v_xs_x27_205_ = lean_array_fset(v_assignments_165_, v_fst_197_, v___x_204_);
v___x_211_ = lean_unbox(v_v_203_);
switch(v___x_211_)
{
case 1:
{
uint8_t v___x_212_; 
lean_dec(v_v_203_);
v___x_212_ = 2;
v___y_207_ = v___x_212_;
goto v___jp_206_;
}
case 3:
{
uint8_t v___x_213_; 
lean_dec(v_v_203_);
v___x_213_ = 0;
v___y_207_ = v___x_213_;
goto v___jp_206_;
}
default: 
{
uint8_t v___x_214_; 
v___x_214_ = lean_unbox(v_v_203_);
lean_dec(v_v_203_);
v___y_207_ = v___x_214_;
goto v___jp_206_;
}
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_box(v___y_207_);
v___x_209_ = lean_array_fset(v_xs_x27_205_, v_fst_197_, v___x_208_);
lean_dec(v_fst_197_);
v___x_210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_210_, 0, v___x_199_);
lean_ctor_set(v___x_210_, 1, v_rupUnits_163_);
lean_ctor_set(v___x_210_, 2, v_ratUnits_164_);
lean_ctor_set(v___x_210_, 3, v___x_209_);
return v___x_210_;
}
}
}
}
else
{
goto v___jp_169_;
}
}
else
{
goto v___jp_169_;
}
v___jp_169_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v_c_161_);
v___x_171_ = lean_array_push(v_clauses_162_, v___x_170_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_171_);
v___x_173_ = v___x_167_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_rupUnits_163_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v_ratUnits_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v_assignments_165_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(lean_object* v_n_216_, lean_object* v_f_217_, lean_object* v_c_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_217_, v_c_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed(lean_object* v_n_220_, lean_object* v_f_221_, lean_object* v_c_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(v_n_220_, v_f_221_, v_c_222_);
lean_dec(v_n_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(lean_object* v_f_224_, lean_object* v_id_225_){
_start:
{
lean_object* v_clauses_226_; lean_object* v_rupUnits_227_; lean_object* v_ratUnits_228_; lean_object* v_assignments_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_260_; 
v_clauses_226_ = lean_ctor_get(v_f_224_, 0);
v_rupUnits_227_ = lean_ctor_get(v_f_224_, 1);
v_ratUnits_228_ = lean_ctor_get(v_f_224_, 2);
v_assignments_229_ = lean_ctor_get(v_f_224_, 3);
v_isSharedCheck_260_ = !lean_is_exclusive(v_f_224_);
if (v_isSharedCheck_260_ == 0)
{
v___x_231_ = v_f_224_;
v_isShared_232_ = v_isSharedCheck_260_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_assignments_229_);
lean_inc(v_ratUnits_228_);
lean_inc(v_rupUnits_227_);
lean_inc(v_clauses_226_);
lean_dec(v_f_224_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_260_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(0);
v___x_240_ = lean_array_get_borrowed(v___x_239_, v_clauses_226_, v_id_225_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_del_object(v___x_231_);
v___x_241_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_241_, 0, v_clauses_226_);
lean_ctor_set(v___x_241_, 1, v_rupUnits_227_);
lean_ctor_set(v___x_241_, 2, v_ratUnits_228_);
lean_ctor_set(v___x_241_, 3, v_assignments_229_);
return v___x_241_;
}
else
{
lean_object* v_val_242_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
if (lean_obj_tag(v_val_242_) == 1)
{
lean_object* v_tail_243_; 
v_tail_243_ = lean_ctor_get(v_val_242_, 1);
if (lean_obj_tag(v_tail_243_) == 0)
{
lean_object* v_head_244_; lean_object* v_fst_245_; lean_object* v_snd_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
lean_del_object(v___x_231_);
v_head_244_ = lean_ctor_get(v_val_242_, 0);
v_fst_245_ = lean_ctor_get(v_head_244_, 0);
lean_inc(v_fst_245_);
v_snd_246_ = lean_ctor_get(v_head_244_, 1);
lean_inc(v_snd_246_);
v___x_247_ = lean_array_set(v_clauses_226_, v_id_225_, v___x_239_);
v___x_248_ = lean_array_get_size(v_assignments_229_);
v___x_249_ = lean_nat_dec_lt(v_fst_245_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_snd_246_);
lean_dec(v_fst_245_);
v___x_250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_250_, 0, v___x_247_);
lean_ctor_set(v___x_250_, 1, v_rupUnits_227_);
lean_ctor_set(v___x_250_, 2, v_ratUnits_228_);
lean_ctor_set(v___x_250_, 3, v_assignments_229_);
return v___x_250_;
}
else
{
lean_object* v_v_251_; lean_object* v___x_252_; lean_object* v_xs_x27_253_; uint8_t v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_v_251_ = lean_array_fget(v_assignments_229_, v_fst_245_);
v___x_252_ = lean_box(0);
v_xs_x27_253_ = lean_array_fset(v_assignments_229_, v_fst_245_, v___x_252_);
v___x_254_ = lean_unbox(v_snd_246_);
lean_dec(v_snd_246_);
v___x_255_ = lean_unbox(v_v_251_);
lean_dec(v_v_251_);
v___x_256_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(v___x_254_, v___x_255_);
v___x_257_ = lean_box(v___x_256_);
v___x_258_ = lean_array_fset(v_xs_x27_253_, v_fst_245_, v___x_257_);
lean_dec(v_fst_245_);
v___x_259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_259_, 0, v___x_247_);
lean_ctor_set(v___x_259_, 1, v_rupUnits_227_);
lean_ctor_set(v___x_259_, 2, v_ratUnits_228_);
lean_ctor_set(v___x_259_, 3, v___x_258_);
return v___x_259_;
}
}
else
{
goto v___jp_233_;
}
}
else
{
goto v___jp_233_;
}
}
v___jp_233_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = lean_box(0);
v___x_235_ = lean_array_set(v_clauses_226_, v_id_225_, v___x_234_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_235_);
v___x_237_ = v___x_231_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_rupUnits_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_ratUnits_228_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_assignments_229_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg___boxed(lean_object* v_f_261_, lean_object* v_id_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(v_f_261_, v_id_262_);
lean_dec(v_id_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(lean_object* v_n_264_, lean_object* v_f_265_, lean_object* v_id_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(v_f_265_, v_id_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___boxed(lean_object* v_n_268_, lean_object* v_f_269_, lean_object* v_id_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(v_n_268_, v_f_269_, v_id_270_);
lean_dec(v_id_270_);
lean_dec(v_n_268_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(lean_object* v_as_272_, size_t v_i_273_, size_t v_stop_274_, lean_object* v_b_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_eq(v_i_273_, v_stop_274_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; size_t v___x_279_; size_t v___x_280_; 
v___x_277_ = lean_array_uget_borrowed(v_as_272_, v_i_273_);
v___x_278_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(v_b_275_, v___x_277_);
v___x_279_ = ((size_t)1ULL);
v___x_280_ = lean_usize_add(v_i_273_, v___x_279_);
v_i_273_ = v___x_280_;
v_b_275_ = v___x_278_;
goto _start;
}
else
{
return v_b_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg___boxed(lean_object* v_as_282_, lean_object* v_i_283_, lean_object* v_stop_284_, lean_object* v_b_285_){
_start:
{
size_t v_i_boxed_286_; size_t v_stop_boxed_287_; lean_object* v_res_288_; 
v_i_boxed_286_ = lean_unbox_usize(v_i_283_);
lean_dec(v_i_283_);
v_stop_boxed_287_ = lean_unbox_usize(v_stop_284_);
lean_dec(v_stop_284_);
v_res_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_as_282_, v_i_boxed_286_, v_stop_boxed_287_, v_b_285_);
lean_dec_ref(v_as_282_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object* v_n_289_, lean_object* v_f_290_, lean_object* v_ids_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_ids_291_);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
return v_f_290_;
}
else
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_le(v___x_293_, v___x_293_);
if (v___x_295_ == 0)
{
if (v___x_294_ == 0)
{
return v_f_290_;
}
else
{
size_t v___x_296_; size_t v___x_297_; lean_object* v___x_298_; 
v___x_296_ = ((size_t)0ULL);
v___x_297_ = lean_usize_of_nat(v___x_293_);
v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_ids_291_, v___x_296_, v___x_297_, v_f_290_);
return v___x_298_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_293_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_ids_291_, v___x_299_, v___x_300_, v_f_290_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed(lean_object* v_n_302_, lean_object* v_f_303_, lean_object* v_ids_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(v_n_302_, v_f_303_, v_ids_304_);
lean_dec_ref(v_ids_304_);
lean_dec(v_n_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(lean_object* v_n_306_, lean_object* v_as_307_, size_t v_i_308_, size_t v_stop_309_, lean_object* v_b_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_as_307_, v_i_308_, v_stop_309_, v_b_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___boxed(lean_object* v_n_312_, lean_object* v_as_313_, lean_object* v_i_314_, lean_object* v_stop_315_, lean_object* v_b_316_){
_start:
{
size_t v_i_boxed_317_; size_t v_stop_boxed_318_; lean_object* v_res_319_; 
v_i_boxed_317_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_stop_boxed_318_ = lean_unbox_usize(v_stop_315_);
lean_dec(v_stop_315_);
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(v_n_312_, v_as_313_, v_i_boxed_317_, v_stop_boxed_318_, v_b_316_);
lean_dec_ref(v_as_313_);
lean_dec(v_n_312_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(lean_object* v_n_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin___boxed(lean_object* v_n_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(v_n_322_);
lean_dec(v_n_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_snd_326_; lean_object* v_fst_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_375_; 
v_snd_326_ = lean_ctor_get(v_x_324_, 1);
lean_inc(v_snd_326_);
v_fst_327_ = lean_ctor_get(v_x_324_, 0);
v_fst_328_ = lean_ctor_get(v_snd_326_, 0);
v_snd_329_ = lean_ctor_get(v_snd_326_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_375_ == 0)
{
v___x_331_ = v_snd_326_;
v_isShared_332_ = v_isSharedCheck_375_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snd_329_);
lean_inc(v_fst_328_);
lean_dec(v_snd_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_375_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_fst_333_; lean_object* v_snd_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v_curAssignment_337_; uint8_t v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; 
v_fst_333_ = lean_ctor_get(v_x_325_, 0);
lean_inc(v_fst_333_);
v_snd_334_ = lean_ctor_get(v_x_325_, 1);
lean_inc(v_snd_334_);
v___x_335_ = 0;
v___x_336_ = lean_box(v___x_335_);
v_curAssignment_337_ = lean_array_get(v___x_336_, v_fst_328_, v_fst_333_);
lean_dec(v___x_336_);
v___x_338_ = lean_unbox(v_snd_334_);
v___x_339_ = lean_unbox(v_curAssignment_337_);
v___x_340_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_372_; 
lean_inc(v_fst_327_);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; lean_object* v_unused_374_; 
v_unused_373_ = lean_ctor_get(v_x_324_, 1);
lean_dec(v_unused_373_);
v_unused_374_ = lean_ctor_get(v_x_324_, 0);
lean_dec(v_unused_374_);
v___x_342_ = v_x_324_;
v_isShared_343_ = v_isSharedCheck_372_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_x_324_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_372_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; lean_object* v_units_345_; lean_object* v___y_347_; uint8_t v___y_348_; lean_object* v___y_357_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_344_ = 1;
v_units_345_ = lean_array_push(v_fst_327_, v_x_325_);
v___x_362_ = lean_array_get_size(v_fst_328_);
v___x_363_ = lean_nat_dec_lt(v_fst_333_, v___x_362_);
if (v___x_363_ == 0)
{
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
v___y_357_ = v_fst_328_;
goto v___jp_356_;
}
else
{
lean_object* v_v_364_; lean_object* v___x_365_; lean_object* v_xs_x27_366_; uint8_t v___x_367_; uint8_t v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_v_364_ = lean_array_fget(v_fst_328_, v_fst_333_);
v___x_365_ = lean_box(0);
v_xs_x27_366_ = lean_array_fset(v_fst_328_, v_fst_333_, v___x_365_);
v___x_367_ = lean_unbox(v_snd_334_);
lean_dec(v_snd_334_);
v___x_368_ = lean_unbox(v_v_364_);
lean_dec(v_v_364_);
v___x_369_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v___x_367_, v___x_368_);
v___x_370_ = lean_box(v___x_369_);
v___x_371_ = lean_array_fset(v_xs_x27_366_, v_fst_333_, v___x_370_);
lean_dec(v_fst_333_);
v___y_357_ = v___x_371_;
goto v___jp_356_;
}
v___jp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_box(v___y_348_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_349_);
lean_ctor_set(v___x_331_, 0, v___y_347_);
v___x_351_ = v___x_331_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v___x_351_);
lean_ctor_set(v___x_342_, 0, v_units_345_);
v___x_353_ = v___x_342_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_units_345_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
v___jp_356_:
{
uint8_t v___x_358_; 
v___x_358_ = lean_unbox(v_snd_329_);
lean_dec(v_snd_329_);
if (v___x_358_ == 0)
{
uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = 3;
v___x_360_ = lean_unbox(v_curAssignment_337_);
lean_dec(v_curAssignment_337_);
v___x_361_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(v___x_360_, v___x_359_);
if (v___x_361_ == 0)
{
v___y_347_ = v___y_357_;
v___y_348_ = v___x_344_;
goto v___jp_346_;
}
else
{
v___y_347_ = v___y_357_;
v___y_348_ = v___x_340_;
goto v___jp_346_;
}
}
else
{
lean_dec(v_curAssignment_337_);
v___y_347_ = v___y_357_;
v___y_348_ = v___x_344_;
goto v___jp_346_;
}
}
}
}
else
{
lean_dec(v_curAssignment_337_);
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
lean_del_object(v___x_331_);
lean_dec(v_snd_329_);
lean_dec(v_fst_328_);
lean_dec_ref(v_x_325_);
return v_x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(lean_object* v_n_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(v_x_377_, v_x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___boxed(lean_object* v_n_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(v_n_380_, v_x_381_, v_x_382_);
lean_dec(v_n_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
return v_x_384_;
}
else
{
lean_object* v_head_386_; lean_object* v_tail_387_; lean_object* v___x_388_; 
v_head_386_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_head_386_);
v_tail_387_ = lean_ctor_get(v_x_385_, 1);
lean_inc(v_tail_387_);
lean_dec_ref_known(v_x_385_, 2);
v___x_388_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(v_x_384_, v_head_386_);
v_x_384_ = v___x_388_;
v_x_385_ = v_tail_387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(lean_object* v_n_390_, lean_object* v_f_391_, lean_object* v_ls_392_){
_start:
{
lean_object* v_clauses_393_; lean_object* v_rupUnits_394_; lean_object* v_ratUnits_395_; lean_object* v_assignments_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_419_; 
v_clauses_393_ = lean_ctor_get(v_f_391_, 0);
v_rupUnits_394_ = lean_ctor_get(v_f_391_, 1);
v_ratUnits_395_ = lean_ctor_get(v_f_391_, 2);
v_assignments_396_ = lean_ctor_get(v_f_391_, 3);
v_isSharedCheck_419_ = !lean_is_exclusive(v_f_391_);
if (v_isSharedCheck_419_ == 0)
{
v___x_398_ = v_f_391_;
v_isShared_399_ = v_isSharedCheck_419_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_assignments_396_);
lean_inc(v_ratUnits_395_);
lean_inc(v_rupUnits_394_);
lean_inc(v_clauses_393_);
lean_dec(v_f_391_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_419_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_snd_405_; lean_object* v_fst_406_; lean_object* v_fst_407_; lean_object* v_snd_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_418_; 
v___x_400_ = 0;
v___x_401_ = lean_box(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_assignments_396_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_rupUnits_394_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v___x_403_, v_ls_392_);
v_snd_405_ = lean_ctor_get(v___x_404_, 1);
lean_inc(v_snd_405_);
v_fst_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_fst_406_);
lean_dec_ref(v___x_404_);
v_fst_407_ = lean_ctor_get(v_snd_405_, 0);
v_snd_408_ = lean_ctor_get(v_snd_405_, 1);
v_isSharedCheck_418_ = !lean_is_exclusive(v_snd_405_);
if (v_isSharedCheck_418_ == 0)
{
v___x_410_ = v_snd_405_;
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snd_408_);
lean_inc(v_fst_407_);
lean_dec(v_snd_405_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 3, v_fst_407_);
lean_ctor_set(v___x_398_, 1, v_fst_406_);
v___x_413_ = v___x_398_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_clauses_393_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_fst_406_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_ratUnits_395_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_fst_407_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_snd_408_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits___boxed(lean_object* v_n_420_, lean_object* v_f_421_, lean_object* v_ls_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(v_n_420_, v_f_421_, v_ls_422_);
lean_dec(v_n_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(lean_object* v_n_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v_x_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___boxed(lean_object* v_n_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(v_n_428_, v_x_429_, v_x_430_);
lean_dec(v_n_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(lean_object* v_f_432_, lean_object* v_ls_433_){
_start:
{
lean_object* v_clauses_434_; lean_object* v_rupUnits_435_; lean_object* v_ratUnits_436_; lean_object* v_assignments_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_460_; 
v_clauses_434_ = lean_ctor_get(v_f_432_, 0);
v_rupUnits_435_ = lean_ctor_get(v_f_432_, 1);
v_ratUnits_436_ = lean_ctor_get(v_f_432_, 2);
v_assignments_437_ = lean_ctor_get(v_f_432_, 3);
v_isSharedCheck_460_ = !lean_is_exclusive(v_f_432_);
if (v_isSharedCheck_460_ == 0)
{
v___x_439_ = v_f_432_;
v_isShared_440_ = v_isSharedCheck_460_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_assignments_437_);
lean_inc(v_ratUnits_436_);
lean_inc(v_rupUnits_435_);
lean_inc(v_clauses_434_);
lean_dec(v_f_432_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_460_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_snd_446_; lean_object* v_fst_447_; lean_object* v_fst_448_; lean_object* v_snd_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_459_; 
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_assignments_437_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_ratUnits_436_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v___x_444_, v_ls_433_);
v_snd_446_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_snd_446_);
v_fst_447_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_fst_447_);
lean_dec_ref(v___x_445_);
v_fst_448_ = lean_ctor_get(v_snd_446_, 0);
v_snd_449_ = lean_ctor_get(v_snd_446_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_snd_446_);
if (v_isSharedCheck_459_ == 0)
{
v___x_451_ = v_snd_446_;
v_isShared_452_ = v_isSharedCheck_459_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_snd_449_);
lean_inc(v_fst_448_);
lean_dec(v_snd_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_459_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 3, v_fst_448_);
lean_ctor_set(v___x_439_, 2, v_fst_447_);
v___x_454_ = v___x_439_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_clauses_434_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_rupUnits_435_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_fst_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_fst_448_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_456_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_snd_449_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(lean_object* v_n_461_, lean_object* v_f_462_, lean_object* v_ls_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(v_f_462_, v_ls_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___boxed(lean_object* v_n_465_, lean_object* v_f_466_, lean_object* v_ls_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(v_n_465_, v_f_466_, v_ls_467_);
lean_dec(v_n_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_fst_471_ = lean_ctor_get(v_x_470_, 0);
v_snd_472_ = lean_ctor_get(v_x_470_, 1);
v___x_473_ = lean_array_get_size(v_x_469_);
v___x_474_ = lean_nat_dec_lt(v_fst_471_, v___x_473_);
if (v___x_474_ == 0)
{
return v_x_469_;
}
else
{
lean_object* v_v_475_; lean_object* v___x_476_; lean_object* v_xs_x27_477_; uint8_t v___x_478_; uint8_t v___x_479_; uint8_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_v_475_ = lean_array_fget(v_x_469_, v_fst_471_);
v___x_476_ = lean_box(0);
v_xs_x27_477_ = lean_array_fset(v_x_469_, v_fst_471_, v___x_476_);
v___x_478_ = lean_unbox(v_snd_472_);
v___x_479_ = lean_unbox(v_v_475_);
lean_dec(v_v_475_);
v___x_480_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(v___x_478_, v___x_479_);
v___x_481_ = lean_box(v___x_480_);
v___x_482_ = lean_array_fset(v_xs_x27_477_, v_fst_471_, v___x_481_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg___boxed(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_483_, v_x_484_);
lean_dec_ref(v_x_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(lean_object* v_n_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_487_, v_x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___boxed(lean_object* v_n_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(v_n_490_, v_x_491_, v_x_492_);
lean_dec_ref(v_x_492_);
lean_dec(v_n_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(lean_object* v_as_494_, size_t v_i_495_, size_t v_stop_496_, lean_object* v_b_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_usize_dec_eq(v_i_495_, v_stop_496_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; size_t v___x_501_; size_t v___x_502_; 
v___x_499_ = lean_array_uget_borrowed(v_as_494_, v_i_495_);
v___x_500_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_b_497_, v___x_499_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_495_, v___x_501_);
v_i_495_ = v___x_502_;
v_b_497_ = v___x_500_;
goto _start;
}
else
{
return v_b_497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg___boxed(lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_, lean_object* v_b_507_){
_start:
{
size_t v_i_boxed_508_; size_t v_stop_boxed_509_; lean_object* v_res_510_; 
v_i_boxed_508_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_509_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_as_504_, v_i_boxed_508_, v_stop_boxed_509_, v_b_507_);
lean_dec_ref(v_as_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(lean_object* v_n_511_, lean_object* v_f_512_){
_start:
{
lean_object* v_clauses_513_; lean_object* v_rupUnits_514_; lean_object* v_ratUnits_515_; lean_object* v_assignments_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_536_; 
v_clauses_513_ = lean_ctor_get(v_f_512_, 0);
v_rupUnits_514_ = lean_ctor_get(v_f_512_, 1);
v_ratUnits_515_ = lean_ctor_get(v_f_512_, 2);
v_assignments_516_ = lean_ctor_get(v_f_512_, 3);
v_isSharedCheck_536_ = !lean_is_exclusive(v_f_512_);
if (v_isSharedCheck_536_ == 0)
{
v___x_518_ = v_f_512_;
v_isShared_519_ = v_isSharedCheck_536_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_assignments_516_);
lean_inc(v_ratUnits_515_);
lean_inc(v_rupUnits_514_);
lean_inc(v_clauses_513_);
lean_dec(v_f_512_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_536_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___y_521_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_array_get_size(v_rupUnits_514_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v_rupUnits_514_);
v___y_521_ = v_assignments_516_;
goto v___jp_520_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_le(v___x_527_, v___x_527_);
if (v___x_529_ == 0)
{
if (v___x_528_ == 0)
{
lean_dec_ref(v_rupUnits_514_);
v___y_521_ = v_assignments_516_;
goto v___jp_520_;
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((size_t)0ULL);
v___x_531_ = lean_usize_of_nat(v___x_527_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_rupUnits_514_, v___x_530_, v___x_531_, v_assignments_516_);
lean_dec_ref(v_rupUnits_514_);
v___y_521_ = v___x_532_;
goto v___jp_520_;
}
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((size_t)0ULL);
v___x_534_ = lean_usize_of_nat(v___x_527_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_rupUnits_514_, v___x_533_, v___x_534_, v_assignments_516_);
lean_dec_ref(v_rupUnits_514_);
v___y_521_ = v___x_535_;
goto v___jp_520_;
}
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 3, v___y_521_);
lean_ctor_set(v___x_518_, 1, v___x_522_);
v___x_524_ = v___x_518_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_clauses_513_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_ratUnits_515_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v___y_521_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits___boxed(lean_object* v_n_537_, lean_object* v_f_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_537_, v_f_538_);
lean_dec(v_n_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(lean_object* v_n_540_, lean_object* v_as_541_, size_t v_i_542_, size_t v_stop_543_, lean_object* v_b_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_as_541_, v_i_542_, v_stop_543_, v_b_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___boxed(lean_object* v_n_546_, lean_object* v_as_547_, lean_object* v_i_548_, lean_object* v_stop_549_, lean_object* v_b_550_){
_start:
{
size_t v_i_boxed_551_; size_t v_stop_boxed_552_; lean_object* v_res_553_; 
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_stop_boxed_552_ = lean_unbox_usize(v_stop_549_);
lean_dec(v_stop_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(v_n_546_, v_as_547_, v_i_boxed_551_, v_stop_boxed_552_, v_b_550_);
lean_dec_ref(v_as_547_);
lean_dec(v_n_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(lean_object* v_f_554_){
_start:
{
lean_object* v_clauses_555_; lean_object* v_rupUnits_556_; lean_object* v_ratUnits_557_; lean_object* v_assignments_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_578_; 
v_clauses_555_ = lean_ctor_get(v_f_554_, 0);
v_rupUnits_556_ = lean_ctor_get(v_f_554_, 1);
v_ratUnits_557_ = lean_ctor_get(v_f_554_, 2);
v_assignments_558_ = lean_ctor_get(v_f_554_, 3);
v_isSharedCheck_578_ = !lean_is_exclusive(v_f_554_);
if (v_isSharedCheck_578_ == 0)
{
v___x_560_ = v_f_554_;
v_isShared_561_ = v_isSharedCheck_578_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_assignments_558_);
lean_inc(v_ratUnits_557_);
lean_inc(v_rupUnits_556_);
lean_inc(v_clauses_555_);
lean_dec(v_f_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_578_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___y_563_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_array_get_size(v_ratUnits_557_);
v___x_570_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_ratUnits_557_);
v___y_563_ = v_assignments_558_;
goto v___jp_562_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = lean_nat_dec_le(v___x_569_, v___x_569_);
if (v___x_571_ == 0)
{
if (v___x_570_ == 0)
{
lean_dec_ref(v_ratUnits_557_);
v___y_563_ = v_assignments_558_;
goto v___jp_562_;
}
else
{
size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
v___x_572_ = ((size_t)0ULL);
v___x_573_ = lean_usize_of_nat(v___x_569_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_ratUnits_557_, v___x_572_, v___x_573_, v_assignments_558_);
lean_dec_ref(v_ratUnits_557_);
v___y_563_ = v___x_574_;
goto v___jp_562_;
}
}
else
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
v___x_575_ = ((size_t)0ULL);
v___x_576_ = lean_usize_of_nat(v___x_569_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_ratUnits_557_, v___x_575_, v___x_576_, v_assignments_558_);
lean_dec_ref(v_ratUnits_557_);
v___y_563_ = v___x_577_;
goto v___jp_562_;
}
}
v___jp_562_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 3, v___y_563_);
lean_ctor_set(v___x_560_, 2, v___x_564_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_clauses_555_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_rupUnits_556_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_567_, 3, v___y_563_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(lean_object* v_n_579_, lean_object* v_f_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v_f_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___boxed(lean_object* v_n_582_, lean_object* v_f_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(v_n_582_, v_f_583_);
lean_dec(v_n_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
return v_x_585_;
}
else
{
lean_object* v_head_587_; lean_object* v_tail_588_; lean_object* v___x_589_; 
v_head_587_ = lean_ctor_get(v_x_586_, 0);
v_tail_588_ = lean_ctor_get(v_x_586_, 1);
v___x_589_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_585_, v_head_587_);
v_x_585_ = v___x_589_;
v_x_586_ = v_tail_588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg___boxed(lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_x_591_, v_x_592_);
lean_dec(v_x_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(lean_object* v_n_594_, lean_object* v_assignments_595_, lean_object* v_derivedLits_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_595_, v_derivedLits_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments___boxed(lean_object* v_n_598_, lean_object* v_assignments_599_, lean_object* v_derivedLits_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(v_n_598_, v_assignments_599_, v_derivedLits_600_);
lean_dec(v_derivedLits_600_);
lean_dec(v_n_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(lean_object* v_n_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_x_603_, v_x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___boxed(lean_object* v_n_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(v_n_606_, v_x_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_n_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(lean_object* v_n_610_, lean_object* v_clauses_611_, lean_object* v_x_612_, lean_object* v_id_613_){
_start:
{
lean_object* v_snd_614_; lean_object* v_snd_615_; lean_object* v_snd_616_; uint8_t v___x_617_; 
v_snd_614_ = lean_ctor_get(v_x_612_, 1);
lean_inc(v_snd_614_);
v_snd_615_ = lean_ctor_get(v_snd_614_, 1);
lean_inc(v_snd_615_);
v_snd_616_ = lean_ctor_get(v_snd_615_, 1);
v___x_617_ = lean_unbox(v_snd_616_);
if (v___x_617_ == 0)
{
lean_object* v_fst_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_698_; 
v_fst_618_ = lean_ctor_get(v_snd_615_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_snd_615_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v_snd_615_, 1);
lean_dec(v_unused_699_);
v___x_620_ = v_snd_615_;
v_isShared_621_ = v_isSharedCheck_698_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_fst_618_);
lean_dec(v_snd_615_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_698_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_unbox(v_fst_618_);
if (v___x_622_ == 0)
{
lean_object* v_fst_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_696_; 
v_fst_623_ = lean_ctor_get(v_x_612_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v_x_612_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_x_612_, 1);
lean_dec(v_unused_697_);
v___x_625_ = v_x_612_;
v_isShared_626_ = v_isSharedCheck_696_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_fst_623_);
lean_dec(v_x_612_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_696_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_fst_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_694_; 
v_fst_627_ = lean_ctor_get(v_snd_614_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_snd_614_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_snd_614_, 1);
lean_dec(v_unused_695_);
v___x_629_ = v_snd_614_;
v_isShared_630_ = v_isSharedCheck_694_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_fst_627_);
lean_dec(v_snd_614_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_694_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
uint8_t v___x_631_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_631_ = 1;
v___x_643_ = lean_array_get_size(v_clauses_611_);
v___x_644_ = lean_nat_dec_lt(v_id_613_, v___x_643_);
if (v___x_644_ == 0)
{
goto v___jp_632_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_array_fget_borrowed(v_clauses_611_, v_id_613_);
if (lean_obj_tag(v___x_645_) == 0)
{
goto v___jp_632_;
}
else
{
lean_object* v_val_646_; lean_object* v___x_647_; 
lean_del_object(v___x_629_);
lean_del_object(v___x_625_);
lean_del_object(v___x_620_);
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
v___x_647_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(v_n_610_, v_val_646_, v_fst_623_);
switch(lean_obj_tag(v___x_647_))
{
case 2:
{
lean_object* v_l_648_; lean_object* v_fst_649_; lean_object* v_snd_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; lean_object* v___y_658_; 
v_l_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_l_648_);
lean_dec_ref_known(v___x_647_, 1);
v_fst_649_ = lean_ctor_get(v_l_648_, 0);
v_snd_650_ = lean_ctor_get(v_l_648_, 1);
v___x_651_ = 0;
v___x_652_ = lean_box(v___x_651_);
v___x_653_ = lean_array_get(v___x_652_, v_fst_623_, v_fst_649_);
lean_dec(v___x_652_);
v___x_654_ = lean_unbox(v_snd_650_);
v___x_655_ = lean_unbox(v___x_653_);
lean_dec(v___x_653_);
v___x_656_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_665_; uint8_t v___x_666_; 
lean_dec(v_fst_618_);
v___x_665_ = lean_array_get_size(v_fst_623_);
v___x_666_ = lean_nat_dec_lt(v_fst_649_, v___x_665_);
if (v___x_666_ == 0)
{
v___y_658_ = v_fst_623_;
goto v___jp_657_;
}
else
{
lean_object* v_v_667_; lean_object* v___x_668_; lean_object* v_xs_x27_669_; uint8_t v___x_670_; uint8_t v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_v_667_ = lean_array_fget(v_fst_623_, v_fst_649_);
v___x_668_ = lean_box(0);
v_xs_x27_669_ = lean_array_fset(v_fst_623_, v_fst_649_, v___x_668_);
v___x_670_ = lean_unbox(v_snd_650_);
v___x_671_ = lean_unbox(v_v_667_);
lean_dec(v_v_667_);
v___x_672_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v___x_670_, v___x_671_);
v___x_673_ = lean_box(v___x_672_);
v___x_674_ = lean_array_fset(v_xs_x27_669_, v_fst_649_, v___x_673_);
v___y_658_ = v___x_674_;
goto v___jp_657_;
}
}
else
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_683_; 
v_isSharedCheck_683_ = !lean_is_exclusive(v_l_648_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; lean_object* v_unused_685_; 
v_unused_684_ = lean_ctor_get(v_l_648_, 1);
lean_dec(v_unused_684_);
v_unused_685_ = lean_ctor_get(v_l_648_, 0);
lean_dec(v_unused_685_);
v___x_676_ = v_l_648_;
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_l_648_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_683_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
lean_inc(v_fst_618_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_fst_618_);
lean_ctor_set(v___x_676_, 0, v_fst_618_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_fst_618_);
v___x_679_ = v_reuseFailAlloc_682_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v_fst_627_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_fst_623_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
}
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v_l_648_);
lean_ctor_set(v___x_659_, 1, v_fst_627_);
v___x_660_ = lean_box(v___x_656_);
v___x_661_ = lean_box(v___x_656_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_659_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_658_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
return v___x_664_;
}
}
case 3:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = lean_box(v___x_631_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v_fst_618_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_fst_627_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_fst_623_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
return v___x_689_;
}
default: 
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v___x_647_);
v___x_690_ = lean_box(v___x_631_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_fst_618_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_fst_627_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_fst_623_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
return v___x_693_;
}
}
}
}
v___jp_632_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_box(v___x_631_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_633_);
v___x_635_ = v___x_620_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_633_);
v___x_635_ = v_reuseFailAlloc_642_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_637_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 1, v___x_635_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_fst_627_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_635_);
v___x_637_ = v_reuseFailAlloc_641_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_637_);
v___x_639_ = v___x_625_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_fst_623_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_620_);
lean_dec(v_fst_618_);
lean_dec(v_snd_614_);
return v_x_612_;
}
}
}
else
{
lean_dec(v_snd_615_);
lean_dec(v_snd_614_);
return v_x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint___boxed(lean_object* v_n_700_, lean_object* v_clauses_701_, lean_object* v_x_702_, lean_object* v_id_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(v_n_700_, v_clauses_701_, v_x_702_, v_id_703_);
lean_dec(v_id_703_);
lean_dec_ref(v_clauses_701_);
lean_dec(v_n_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(lean_object* v_n_705_, lean_object* v_clauses_706_, lean_object* v_as_707_, size_t v_i_708_, size_t v_stop_709_, lean_object* v_b_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = lean_usize_dec_eq(v_i_708_, v_stop_709_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; size_t v___x_714_; size_t v___x_715_; 
v___x_712_ = lean_array_uget_borrowed(v_as_707_, v_i_708_);
v___x_713_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(v_n_705_, v_clauses_706_, v_b_710_, v___x_712_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_708_, v___x_714_);
v_i_708_ = v___x_715_;
v_b_710_ = v___x_713_;
goto _start;
}
else
{
return v_b_710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0___boxed(lean_object* v_n_717_, lean_object* v_clauses_718_, lean_object* v_as_719_, lean_object* v_i_720_, lean_object* v_stop_721_, lean_object* v_b_722_){
_start:
{
size_t v_i_boxed_723_; size_t v_stop_boxed_724_; lean_object* v_res_725_; 
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_stop_boxed_724_ = lean_unbox_usize(v_stop_721_);
lean_dec(v_stop_721_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_717_, v_clauses_718_, v_as_719_, v_i_boxed_723_, v_stop_boxed_724_, v_b_722_);
lean_dec_ref(v_as_719_);
lean_dec_ref(v_clauses_718_);
lean_dec(v_n_717_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(lean_object* v_n_733_, lean_object* v_f_734_, lean_object* v_rupHints_735_){
_start:
{
lean_object* v_clauses_736_; lean_object* v_rupUnits_737_; lean_object* v_ratUnits_738_; lean_object* v_assignments_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_766_; 
v_clauses_736_ = lean_ctor_get(v_f_734_, 0);
v_rupUnits_737_ = lean_ctor_get(v_f_734_, 1);
v_ratUnits_738_ = lean_ctor_get(v_f_734_, 2);
v_assignments_739_ = lean_ctor_get(v_f_734_, 3);
v_isSharedCheck_766_ = !lean_is_exclusive(v_f_734_);
if (v_isSharedCheck_766_ == 0)
{
v___x_741_ = v_f_734_;
v_isShared_742_ = v_isSharedCheck_766_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_assignments_739_);
lean_inc(v_ratUnits_738_);
lean_inc(v_rupUnits_737_);
lean_inc(v_clauses_736_);
lean_dec(v_f_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_766_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_fst_744_; lean_object* v_snd_745_; lean_object* v___y_751_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_754_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1));
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_rupHints_735_);
v___x_757_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
v_fst_744_ = v_assignments_739_;
v_snd_745_ = v___x_754_;
goto v___jp_743_;
}
else
{
lean_object* v___x_758_; uint8_t v___x_759_; 
lean_inc_ref(v_assignments_739_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_assignments_739_);
lean_ctor_set(v___x_758_, 1, v___x_754_);
v___x_759_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_759_ == 0)
{
if (v___x_757_ == 0)
{
lean_dec_ref_known(v___x_758_, 2);
v_fst_744_ = v_assignments_739_;
v_snd_745_ = v___x_754_;
goto v___jp_743_;
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
lean_dec_ref(v_assignments_739_);
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_756_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_733_, v_clauses_736_, v_rupHints_735_, v___x_760_, v___x_761_, v___x_758_);
v___y_751_ = v___x_762_;
goto v___jp_750_;
}
}
else
{
size_t v___x_763_; size_t v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v_assignments_739_);
v___x_763_ = ((size_t)0ULL);
v___x_764_ = lean_usize_of_nat(v___x_756_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_733_, v_clauses_736_, v_rupHints_735_, v___x_763_, v___x_764_, v___x_758_);
v___y_751_ = v___x_765_;
goto v___jp_750_;
}
}
v___jp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 3, v_fst_744_);
v___x_747_ = v___x_741_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_clauses_736_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_rupUnits_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_ratUnits_738_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_fst_744_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_snd_745_);
return v___x_748_;
}
}
v___jp_750_:
{
lean_object* v_fst_752_; lean_object* v_snd_753_; 
v_fst_752_ = lean_ctor_get(v___y_751_, 0);
lean_inc(v_fst_752_);
v_snd_753_ = lean_ctor_get(v___y_751_, 1);
lean_inc(v_snd_753_);
lean_dec_ref(v___y_751_);
v_fst_744_ = v_fst_752_;
v_snd_745_ = v_snd_753_;
goto v___jp_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___boxed(lean_object* v_n_767_, lean_object* v_f_768_, lean_object* v_rupHints_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_767_, v_f_768_, v_rupHints_769_);
lean_dec_ref(v_rupHints_769_);
lean_dec(v_n_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
if (lean_obj_tag(v_a_771_) == 0)
{
lean_object* v___x_773_; 
v___x_773_ = l_List_reverse___redArg(v_a_772_);
return v___x_773_;
}
else
{
lean_object* v_head_774_; lean_object* v_tail_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_809_; 
v_head_774_ = lean_ctor_get(v_a_771_, 0);
v_tail_775_ = lean_ctor_get(v_a_771_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v_a_771_);
if (v_isSharedCheck_809_ == 0)
{
v___x_777_ = v_a_771_;
v_isShared_778_ = v_isSharedCheck_809_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_tail_775_);
lean_inc(v_head_774_);
lean_dec(v_a_771_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_809_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___y_780_; lean_object* v_snd_785_; uint8_t v___x_786_; 
v_snd_785_ = lean_ctor_get(v_head_774_, 1);
v___x_786_ = lean_unbox(v_snd_785_);
if (v___x_786_ == 0)
{
lean_object* v_fst_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v_fst_787_ = lean_ctor_get(v_head_774_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_head_774_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_head_774_, 1);
lean_dec(v_unused_797_);
v___x_789_ = v_head_774_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_fst_787_);
lean_dec(v_head_774_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = 1;
v___x_792_ = lean_box(v___x_791_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 1, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_fst_787_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v___y_780_ = v___x_794_;
goto v___jp_779_;
}
}
}
else
{
lean_object* v_fst_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_807_; 
v_fst_798_ = lean_ctor_get(v_head_774_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_head_774_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_head_774_, 1);
lean_dec(v_unused_808_);
v___x_800_ = v_head_774_;
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_fst_798_);
lean_dec(v_head_774_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_807_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_802_ = 0;
v___x_803_ = lean_box(v___x_802_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v___x_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_fst_798_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
v___y_780_ = v___x_805_;
goto v___jp_779_;
}
}
}
v___jp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_a_772_);
lean_ctor_set(v___x_777_, 0, v___y_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___y_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_772_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v_a_771_ = v_tail_775_;
v_a_772_ = v___x_782_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object* v_n_810_, lean_object* v_f_811_, lean_object* v_c_812_, lean_object* v_rupHints_813_){
_start:
{
lean_object* v___x_814_; lean_object* v_negC_815_; lean_object* v___x_816_; lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_876_; 
v___x_814_ = lean_box(0);
lean_inc(v_c_812_);
v_negC_815_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v_c_812_, v___x_814_);
v___x_816_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(v_n_810_, v_f_811_, v_negC_815_);
v_fst_817_ = lean_ctor_get(v___x_816_, 0);
v_snd_818_ = lean_ctor_get(v___x_816_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_876_ == 0)
{
v___x_820_ = v___x_816_;
v_isShared_821_ = v_isSharedCheck_876_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_817_);
lean_dec(v___x_816_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_876_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 1;
v___x_823_ = lean_unbox(v_snd_818_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v_snd_825_; lean_object* v_snd_826_; lean_object* v_snd_827_; uint8_t v___x_828_; 
lean_del_object(v___x_820_);
v___x_824_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_810_, v_fst_817_, v_rupHints_813_);
v_snd_825_ = lean_ctor_get(v___x_824_, 1);
lean_inc(v_snd_825_);
v_snd_826_ = lean_ctor_get(v_snd_825_, 1);
lean_inc(v_snd_826_);
v_snd_827_ = lean_ctor_get(v_snd_826_, 1);
v___x_828_ = lean_unbox(v_snd_827_);
if (v___x_828_ == 0)
{
lean_object* v_fst_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_858_; 
lean_inc(v_snd_827_);
lean_dec(v_snd_818_);
v_fst_829_ = lean_ctor_get(v_snd_826_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_snd_826_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_snd_826_, 1);
lean_dec(v_unused_859_);
v___x_831_ = v_snd_826_;
v_isShared_832_ = v_isSharedCheck_858_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_fst_829_);
lean_dec(v_snd_826_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_858_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = lean_unbox(v_fst_829_);
lean_dec(v_fst_829_);
if (v___x_833_ == 0)
{
lean_object* v_fst_834_; lean_object* v___x_836_; 
lean_dec(v_snd_825_);
lean_dec(v_c_812_);
v_fst_834_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_fst_834_);
lean_dec_ref(v___x_824_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v_fst_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_snd_827_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v_fst_838_; lean_object* v_fst_839_; lean_object* v_clauses_840_; lean_object* v_rupUnits_841_; lean_object* v_ratUnits_842_; lean_object* v_assignments_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_snd_827_);
v_fst_838_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_fst_838_);
lean_dec_ref(v___x_824_);
v_fst_839_ = lean_ctor_get(v_snd_825_, 0);
lean_inc(v_fst_839_);
lean_dec(v_snd_825_);
v_clauses_840_ = lean_ctor_get(v_fst_838_, 0);
v_rupUnits_841_ = lean_ctor_get(v_fst_838_, 1);
v_ratUnits_842_ = lean_ctor_get(v_fst_838_, 2);
v_assignments_843_ = lean_ctor_get(v_fst_838_, 3);
v_isSharedCheck_857_ = !lean_is_exclusive(v_fst_838_);
if (v_isSharedCheck_857_ == 0)
{
v___x_845_ = v_fst_838_;
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_assignments_843_);
lean_inc(v_ratUnits_842_);
lean_inc(v_rupUnits_841_);
lean_inc(v_clauses_840_);
lean_dec(v_fst_838_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_assignments_847_; lean_object* v___x_849_; 
v_assignments_847_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_843_, v_fst_839_);
lean_dec(v_fst_839_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 3, v_assignments_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_clauses_840_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_rupUnits_841_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_ratUnits_842_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_assignments_847_);
v___x_849_ = v_reuseFailAlloc_856_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v_f_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v_f_850_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_810_, v___x_849_);
v___x_851_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_850_, v_c_812_);
v___x_852_ = lean_box(v___x_822_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_852_);
lean_ctor_set(v___x_831_, 0, v___x_851_);
v___x_854_ = v___x_831_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
else
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_snd_825_);
lean_dec(v_c_812_);
v_isSharedCheck_867_ = !lean_is_exclusive(v_snd_826_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_868_ = lean_ctor_get(v_snd_826_, 1);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_snd_826_, 0);
lean_dec(v_unused_869_);
v___x_861_ = v_snd_826_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_dec(v_snd_826_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; lean_object* v___x_865_; 
v_fst_863_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_fst_863_);
lean_dec_ref(v___x_824_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_snd_818_);
lean_ctor_set(v___x_861_, 0, v_fst_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_fst_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_snd_818_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_f_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec(v_snd_818_);
v_f_870_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_810_, v_fst_817_);
v___x_871_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_870_, v_c_812_);
v___x_872_ = lean_box(v___x_822_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_872_);
lean_ctor_set(v___x_820_, 0, v___x_871_);
v___x_874_ = v___x_820_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(lean_object* v_n_877_, lean_object* v_f_878_, lean_object* v_c_879_, lean_object* v_rupHints_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_877_, v_f_878_, v_c_879_, v_rupHints_880_);
lean_dec_ref(v_rupHints_880_);
lean_dec(v_n_877_);
return v_res_881_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(lean_object* v_a_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
uint8_t v___x_884_; 
v___x_884_ = 0;
return v___x_884_;
}
else
{
lean_object* v_head_885_; lean_object* v_tail_886_; uint8_t v___y_888_; lean_object* v_fst_890_; lean_object* v_snd_891_; lean_object* v_fst_892_; lean_object* v_snd_893_; uint8_t v___x_894_; 
v_head_885_ = lean_ctor_get(v_x_883_, 0);
v_tail_886_ = lean_ctor_get(v_x_883_, 1);
v_fst_890_ = lean_ctor_get(v_a_882_, 0);
v_snd_891_ = lean_ctor_get(v_a_882_, 1);
v_fst_892_ = lean_ctor_get(v_head_885_, 0);
v_snd_893_ = lean_ctor_get(v_head_885_, 1);
v___x_894_ = lean_nat_dec_eq(v_fst_890_, v_fst_892_);
if (v___x_894_ == 0)
{
v_x_883_ = v_tail_886_;
goto _start;
}
else
{
uint8_t v___x_896_; 
v___x_896_ = lean_unbox(v_snd_893_);
if (v___x_896_ == 0)
{
uint8_t v___x_897_; 
v___x_897_ = lean_unbox(v_snd_891_);
if (v___x_897_ == 0)
{
v___y_888_ = v___x_894_;
goto v___jp_887_;
}
else
{
v_x_883_ = v_tail_886_;
goto _start;
}
}
else
{
uint8_t v___x_899_; 
v___x_899_ = lean_unbox(v_snd_891_);
v___y_888_ = v___x_899_;
goto v___jp_887_;
}
}
v___jp_887_:
{
if (v___y_888_ == 0)
{
v_x_883_ = v_tail_886_;
goto _start;
}
else
{
return v___y_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg___boxed(lean_object* v_a_900_, lean_object* v_x_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_a_900_, v_x_901_);
lean_dec(v_x_901_);
lean_dec_ref(v_a_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(lean_object* v_clauses_904_, lean_object* v_n_905_, lean_object* v___y_906_, lean_object* v_as_907_, size_t v_i_908_, size_t v_stop_909_, lean_object* v_b_910_){
_start:
{
lean_object* v___y_912_; uint8_t v___x_916_; 
v___x_916_ = lean_usize_dec_eq(v_i_908_, v_stop_909_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_array_uget_borrowed(v_as_907_, v_i_908_);
v___x_919_ = lean_array_get_borrowed(v___x_917_, v_clauses_904_, v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
v___y_912_ = v_b_910_;
goto v___jp_911_;
}
else
{
lean_object* v_val_920_; uint8_t v___x_921_; 
v_val_920_ = lean_ctor_get(v___x_919_, 0);
v___x_921_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v___y_906_, v_val_920_);
if (v___x_921_ == 0)
{
v___y_912_ = v_b_910_;
goto v___jp_911_;
}
else
{
lean_object* v___x_922_; 
lean_inc(v___x_918_);
v___x_922_ = lean_array_push(v_b_910_, v___x_918_);
v___y_912_ = v___x_922_;
goto v___jp_911_;
}
}
}
else
{
return v_b_910_;
}
v___jp_911_:
{
size_t v___x_913_; size_t v___x_914_; 
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_add(v_i_908_, v___x_913_);
v_i_908_ = v___x_914_;
v_b_910_ = v___y_912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1___boxed(lean_object* v_clauses_923_, lean_object* v_n_924_, lean_object* v___y_925_, lean_object* v_as_926_, lean_object* v_i_927_, lean_object* v_stop_928_, lean_object* v_b_929_){
_start:
{
size_t v_i_boxed_930_; size_t v_stop_boxed_931_; lean_object* v_res_932_; 
v_i_boxed_930_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_stop_boxed_931_ = lean_unbox_usize(v_stop_928_);
lean_dec(v_stop_928_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_923_, v_n_924_, v___y_925_, v_as_926_, v_i_boxed_930_, v_stop_boxed_931_, v_b_929_);
lean_dec_ref(v_as_926_);
lean_dec_ref(v___y_925_);
lean_dec(v_n_924_);
lean_dec_ref(v_clauses_923_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(lean_object* v_n_935_, lean_object* v_clauses_936_, lean_object* v_l_937_){
_start:
{
lean_object* v___y_939_; lean_object* v_snd_953_; uint8_t v___x_954_; 
v_snd_953_ = lean_ctor_get(v_l_937_, 1);
v___x_954_ = lean_unbox(v_snd_953_);
if (v___x_954_ == 0)
{
lean_object* v_fst_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_964_; 
v_fst_955_ = lean_ctor_get(v_l_937_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_l_937_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_l_937_, 1);
lean_dec(v_unused_965_);
v___x_957_ = v_l_937_;
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_fst_955_);
lean_dec(v_l_937_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_959_ = 1;
v___x_960_ = lean_box(v___x_959_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_960_);
v___x_962_ = v___x_957_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v___y_939_ = v___x_962_;
goto v___jp_938_;
}
}
}
else
{
lean_object* v_fst_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v_fst_966_ = lean_ctor_get(v_l_937_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v_l_937_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v_l_937_, 1);
lean_dec(v_unused_976_);
v___x_968_ = v_l_937_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_fst_966_);
lean_dec(v_l_937_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
uint8_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = 0;
v___x_971_ = lean_box(v___x_970_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_fst_966_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v___y_939_ = v___x_973_;
goto v___jp_938_;
}
}
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_940_ = lean_array_get_size(v_clauses_936_);
v___x_941_ = l_Array_range(v___x_940_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_array_get_size(v___x_941_);
v___x_944_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0));
v___x_945_ = lean_nat_dec_lt(v___x_942_, v___x_943_);
if (v___x_945_ == 0)
{
lean_dec_ref(v___x_941_);
lean_dec_ref(v___y_939_);
return v___x_944_;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_nat_dec_le(v___x_943_, v___x_943_);
if (v___x_946_ == 0)
{
if (v___x_945_ == 0)
{
lean_dec_ref(v___x_941_);
lean_dec_ref(v___y_939_);
return v___x_944_;
}
else
{
size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
v___x_947_ = ((size_t)0ULL);
v___x_948_ = lean_usize_of_nat(v___x_943_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_936_, v_n_935_, v___y_939_, v___x_941_, v___x_947_, v___x_948_, v___x_944_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___y_939_);
return v___x_949_;
}
}
else
{
size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; 
v___x_950_ = ((size_t)0ULL);
v___x_951_ = lean_usize_of_nat(v___x_943_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_936_, v_n_935_, v___y_939_, v___x_941_, v___x_950_, v___x_951_, v___x_944_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___y_939_);
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___boxed(lean_object* v_n_977_, lean_object* v_clauses_978_, lean_object* v_l_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(v_n_977_, v_clauses_978_, v_l_979_);
lean_dec_ref(v_clauses_978_);
lean_dec(v_n_977_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(lean_object* v_n_981_, lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_a_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___boxed(lean_object* v_n_985_, lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(v_n_985_, v_a_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_n_985_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(size_t v_sz_990_, size_t v_i_991_, lean_object* v_bs_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_991_, v_sz_990_);
if (v___x_993_ == 0)
{
return v_bs_992_;
}
else
{
lean_object* v_v_994_; lean_object* v_fst_995_; lean_object* v___x_996_; lean_object* v_bs_x27_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v_v_994_ = lean_array_uget_borrowed(v_bs_992_, v_i_991_);
v_fst_995_ = lean_ctor_get(v_v_994_, 0);
lean_inc(v_fst_995_);
v___x_996_ = lean_unsigned_to_nat(0u);
v_bs_x27_997_ = lean_array_uset(v_bs_992_, v_i_991_, v___x_996_);
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_991_, v___x_998_);
v___x_1000_ = lean_array_uset(v_bs_x27_997_, v_i_991_, v_fst_995_);
v_i_991_ = v___x_999_;
v_bs_992_ = v___x_1000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0___boxed(lean_object* v_sz_1002_, lean_object* v_i_1003_, lean_object* v_bs_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(lean_object* v_xs_1008_, lean_object* v_ys_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_zero_1011_; uint8_t v_isZero_1012_; 
v_zero_1011_ = lean_unsigned_to_nat(0u);
v_isZero_1012_ = lean_nat_dec_eq(v_x_1010_, v_zero_1011_);
if (v_isZero_1012_ == 1)
{
lean_dec(v_x_1010_);
return v_isZero_1012_;
}
else
{
lean_object* v_one_1013_; lean_object* v_n_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_one_1013_ = lean_unsigned_to_nat(1u);
v_n_1014_ = lean_nat_sub(v_x_1010_, v_one_1013_);
lean_dec(v_x_1010_);
v___x_1015_ = lean_array_fget_borrowed(v_xs_1008_, v_n_1014_);
v___x_1016_ = lean_array_fget_borrowed(v_ys_1009_, v_n_1014_);
v___x_1017_ = lean_nat_dec_eq(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_n_1014_);
return v___x_1017_;
}
else
{
v_x_1010_ = v_n_1014_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg___boxed(lean_object* v_xs_1019_, lean_object* v_ys_1020_, lean_object* v_x_1021_){
_start:
{
uint8_t v_res_1022_; lean_object* v_r_1023_; 
v_res_1022_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_1019_, v_ys_1020_, v_x_1021_);
lean_dec_ref(v_ys_1020_);
lean_dec_ref(v_xs_1019_);
v_r_1023_ = lean_box(v_res_1022_);
return v_r_1023_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(lean_object* v_xs_1024_, lean_object* v_ys_1025_){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_array_get_size(v_xs_1024_);
v___x_1027_ = lean_array_get_size(v_ys_1025_);
v___x_1028_ = lean_nat_dec_eq(v___x_1026_, v___x_1027_);
if (v___x_1028_ == 0)
{
return v___x_1028_;
}
else
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_1024_, v_ys_1025_, v___x_1026_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1___boxed(lean_object* v_xs_1030_, lean_object* v_ys_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(v_xs_1030_, v_ys_1031_);
lean_dec_ref(v_ys_1031_);
lean_dec_ref(v_xs_1030_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(lean_object* v_n_1034_, lean_object* v_f_1035_, lean_object* v_pivot_1036_, lean_object* v_ratHints_1037_){
_start:
{
lean_object* v_clauses_1038_; lean_object* v_ratClauseIndices_1039_; size_t v_sz_1040_; size_t v___x_1041_; lean_object* v_ratHintIndices_1042_; uint8_t v___x_1043_; 
v_clauses_1038_ = lean_ctor_get(v_f_1035_, 0);
v_ratClauseIndices_1039_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(v_n_1034_, v_clauses_1038_, v_pivot_1036_);
v_sz_1040_ = lean_array_size(v_ratHints_1037_);
v___x_1041_ = ((size_t)0ULL);
v_ratHintIndices_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(v_sz_1040_, v___x_1041_, v_ratHints_1037_);
v___x_1043_ = l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(v_ratClauseIndices_1039_, v_ratHintIndices_1042_);
lean_dec_ref(v_ratHintIndices_1042_);
lean_dec_ref(v_ratClauseIndices_1039_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive___boxed(lean_object* v_n_1044_, lean_object* v_f_1045_, lean_object* v_pivot_1046_, lean_object* v_ratHints_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(v_n_1044_, v_f_1045_, v_pivot_1046_, v_ratHints_1047_);
lean_dec_ref(v_f_1045_);
lean_dec(v_n_1044_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(lean_object* v_xs_1050_, lean_object* v_ys_1051_, lean_object* v_hsz_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
uint8_t v___x_1055_; 
v___x_1055_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_1050_, v_ys_1051_, v_x_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___boxed(lean_object* v_xs_1056_, lean_object* v_ys_1057_, lean_object* v_hsz_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(v_xs_1056_, v_ys_1057_, v_hsz_1058_, v_x_1059_, v_x_1060_);
lean_dec_ref(v_ys_1057_);
lean_dec_ref(v_xs_1056_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(lean_object* v_as_1063_, size_t v_i_1064_, size_t v_stop_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_usize_dec_eq(v_i_1064_, v_stop_1065_);
if (v___x_1067_ == 0)
{
size_t v___x_1068_; size_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1068_ = ((size_t)1ULL);
v___x_1069_ = lean_usize_sub(v_i_1064_, v___x_1068_);
v___x_1070_ = lean_array_uget_borrowed(v_as_1063_, v___x_1069_);
lean_inc(v___x_1070_);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_b_1066_);
v_i_1064_ = v___x_1069_;
v_b_1066_ = v___x_1071_;
goto _start;
}
else
{
return v_b_1066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0___boxed(lean_object* v_as_1073_, lean_object* v_i_1074_, lean_object* v_stop_1075_, lean_object* v_b_1076_){
_start:
{
size_t v_i_boxed_1077_; size_t v_stop_boxed_1078_; lean_object* v_res_1079_; 
v_i_boxed_1077_ = lean_unbox_usize(v_i_1074_);
lean_dec(v_i_1074_);
v_stop_boxed_1078_ = lean_unbox_usize(v_stop_1075_);
lean_dec(v_stop_1075_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(v_as_1073_, v_i_boxed_1077_, v_stop_boxed_1078_, v_b_1076_);
lean_dec_ref(v_as_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(lean_object* v_l_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
if (lean_obj_tag(v_a_1082_) == 0)
{
lean_dec_ref(v_a_1083_);
lean_inc(v_l_1080_);
return v_l_1080_;
}
else
{
lean_object* v_head_1084_; lean_object* v_tail_1085_; uint8_t v___y_1090_; lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v_fst_1099_; lean_object* v_snd_1100_; uint8_t v___x_1101_; 
v_head_1084_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_head_1084_);
v_tail_1085_ = lean_ctor_get(v_a_1082_, 1);
lean_inc(v_tail_1085_);
lean_dec_ref_known(v_a_1082_, 2);
v_fst_1097_ = lean_ctor_get(v_head_1084_, 0);
v_snd_1098_ = lean_ctor_get(v_head_1084_, 1);
v_fst_1099_ = lean_ctor_get(v_a_1081_, 0);
v_snd_1100_ = lean_ctor_get(v_a_1081_, 1);
v___x_1101_ = lean_nat_dec_eq(v_fst_1097_, v_fst_1099_);
if (v___x_1101_ == 0)
{
goto v___jp_1086_;
}
else
{
uint8_t v___x_1102_; 
v___x_1102_ = lean_unbox(v_snd_1100_);
if (v___x_1102_ == 0)
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_unbox(v_snd_1098_);
if (v___x_1103_ == 0)
{
v___y_1090_ = v___x_1101_;
goto v___jp_1089_;
}
else
{
goto v___jp_1086_;
}
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_unbox(v_snd_1098_);
v___y_1090_ = v___x_1104_;
goto v___jp_1089_;
}
}
v___jp_1086_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_array_push(v_a_1083_, v_head_1084_);
v_a_1082_ = v_tail_1085_;
v_a_1083_ = v___x_1087_;
goto _start;
}
v___jp_1089_:
{
if (v___y_1090_ == 0)
{
goto v___jp_1086_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
lean_dec(v_head_1084_);
v___x_1091_ = lean_array_get_size(v_a_1083_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_nat_dec_lt(v___x_1092_, v___x_1091_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v_a_1083_);
return v_tail_1085_;
}
else
{
size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_usize_of_nat(v___x_1091_);
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(v_a_1083_, v___x_1094_, v___x_1095_, v_tail_1085_);
lean_dec_ref(v_a_1083_);
return v___x_1096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg___boxed(lean_object* v_l_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_l_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec_ref(v_a_1106_);
lean_dec(v_l_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(lean_object* v_n_1110_, lean_object* v_f_1111_, lean_object* v_negPivot_1112_, lean_object* v_ratHint_1113_){
_start:
{
lean_object* v_clauses_1114_; lean_object* v_rupUnits_1115_; lean_object* v_ratUnits_1116_; lean_object* v_assignments_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1195_; 
v_clauses_1114_ = lean_ctor_get(v_f_1111_, 0);
v_rupUnits_1115_ = lean_ctor_get(v_f_1111_, 1);
v_ratUnits_1116_ = lean_ctor_get(v_f_1111_, 2);
v_assignments_1117_ = lean_ctor_get(v_f_1111_, 3);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_f_1111_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1119_ = v_f_1111_;
v_isShared_1120_ = v_isSharedCheck_1195_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_assignments_1117_);
lean_inc(v_ratUnits_1116_);
lean_inc(v_rupUnits_1115_);
lean_inc(v_clauses_1114_);
lean_dec(v_f_1111_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1195_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1194_; 
v_fst_1121_ = lean_ctor_get(v_ratHint_1113_, 0);
v_snd_1122_ = lean_ctor_get(v_ratHint_1113_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_ratHint_1113_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1124_ = v_ratHint_1113_;
v_isShared_1125_ = v_isSharedCheck_1194_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snd_1122_);
lean_inc(v_fst_1121_);
lean_dec(v_ratHint_1113_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1194_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = lean_array_get_borrowed(v___x_1126_, v_clauses_1114_, v_fst_1121_);
lean_dec(v_fst_1121_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v___x_1129_; 
lean_dec(v_snd_1122_);
if (v_isShared_1120_ == 0)
{
v___x_1129_ = v___x_1119_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_clauses_1114_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_rupUnits_1115_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_ratUnits_1116_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_assignments_1117_);
v___x_1129_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1130_ = 0;
v___x_1131_ = lean_box(v___x_1130_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 1, v___x_1131_);
lean_ctor_set(v___x_1124_, 0, v___x_1129_);
v___x_1133_ = v___x_1124_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_val_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_negC_1140_; lean_object* v___x_1142_; 
lean_del_object(v___x_1124_);
v_val_1136_ = lean_ctor_get(v___x_1127_, 0);
v___x_1137_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
lean_inc(v_val_1136_);
v___x_1138_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_val_1136_, v_negPivot_1112_, v_val_1136_, v___x_1137_);
v___x_1139_ = lean_box(0);
v_negC_1140_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v___x_1138_, v___x_1139_);
if (v_isShared_1120_ == 0)
{
v___x_1142_ = v___x_1119_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_clauses_1114_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_rupUnits_1115_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_ratUnits_1116_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_assignments_1117_);
v___x_1142_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1192_; 
v___x_1143_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(v___x_1142_, v_negC_1140_);
v_fst_1144_ = lean_ctor_get(v___x_1143_, 0);
v_snd_1145_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1192_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_inc(v_fst_1144_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1192_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
uint8_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 1;
v___x_1150_ = lean_unbox(v_snd_1145_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v_snd_1152_; lean_object* v_snd_1153_; lean_object* v_fst_1154_; lean_object* v_fst_1155_; lean_object* v_fst_1156_; lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1186_; 
lean_del_object(v___x_1147_);
v___x_1151_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_1110_, v_fst_1144_, v_snd_1122_);
lean_dec(v_snd_1122_);
v_snd_1152_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1152_);
v_snd_1153_ = lean_ctor_get(v_snd_1152_, 1);
lean_inc(v_snd_1153_);
v_fst_1154_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_fst_1154_);
lean_dec_ref(v___x_1151_);
v_fst_1155_ = lean_ctor_get(v_snd_1152_, 0);
lean_inc(v_fst_1155_);
lean_dec(v_snd_1152_);
v_fst_1156_ = lean_ctor_get(v_snd_1153_, 0);
v_snd_1157_ = lean_ctor_get(v_snd_1153_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_snd_1153_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1159_ = v_snd_1153_;
v_isShared_1160_ = v_isSharedCheck_1186_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_inc(v_fst_1156_);
lean_dec(v_snd_1153_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1186_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_clauses_1161_; lean_object* v_rupUnits_1162_; lean_object* v_ratUnits_1163_; lean_object* v_assignments_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1185_; 
v_clauses_1161_ = lean_ctor_get(v_fst_1154_, 0);
v_rupUnits_1162_ = lean_ctor_get(v_fst_1154_, 1);
v_ratUnits_1163_ = lean_ctor_get(v_fst_1154_, 2);
v_assignments_1164_ = lean_ctor_get(v_fst_1154_, 3);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_fst_1154_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1166_ = v_fst_1154_;
v_isShared_1167_ = v_isSharedCheck_1185_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_assignments_1164_);
lean_inc(v_ratUnits_1163_);
lean_inc(v_rupUnits_1162_);
lean_inc(v_clauses_1161_);
lean_dec(v_fst_1154_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1185_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_assignments_1168_; lean_object* v___x_1170_; 
v_assignments_1168_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_1164_, v_fst_1155_);
lean_dec(v_fst_1155_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 3, v_assignments_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_clauses_1161_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_rupUnits_1162_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_ratUnits_1163_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_assignments_1168_);
v___x_1170_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v_f_1171_; uint8_t v___x_1172_; 
v_f_1171_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v___x_1170_);
v___x_1172_ = lean_unbox(v_snd_1157_);
lean_dec(v_snd_1157_);
if (v___x_1172_ == 0)
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_unbox(v_fst_1156_);
lean_dec(v_fst_1156_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1175_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_snd_1145_);
lean_ctor_set(v___x_1159_, 0, v_f_1171_);
v___x_1175_ = v___x_1159_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_f_1171_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_snd_1145_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_dec(v_snd_1145_);
v___x_1177_ = lean_box(v___x_1149_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1177_);
lean_ctor_set(v___x_1159_, 0, v_f_1171_);
v___x_1179_ = v___x_1159_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_f_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
lean_object* v___x_1182_; 
lean_dec(v_fst_1156_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_snd_1145_);
lean_ctor_set(v___x_1159_, 0, v_f_1171_);
v___x_1182_ = v___x_1159_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_f_1171_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_snd_1145_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
else
{
lean_object* v_f_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_dec(v_snd_1145_);
lean_dec(v_snd_1122_);
v_f_1187_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v_fst_1144_);
v___x_1188_ = lean_box(v___x_1149_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1188_);
lean_ctor_set(v___x_1147_, 0, v_f_1187_);
v___x_1190_ = v___x_1147_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_f_1187_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___boxed(lean_object* v_n_1196_, lean_object* v_f_1197_, lean_object* v_negPivot_1198_, lean_object* v_ratHint_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(v_n_1196_, v_f_1197_, v_negPivot_1198_, v_ratHint_1199_);
lean_dec_ref(v_negPivot_1198_);
lean_dec(v_n_1196_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(lean_object* v_n_1201_, lean_object* v_l_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_l_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___boxed(lean_object* v_n_1207_, lean_object* v_l_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(v_n_1207_, v_l_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec_ref(v_a_1209_);
lean_dec(v_l_1208_);
lean_dec(v_n_1207_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(lean_object* v_pivot_1213_, lean_object* v_n_1214_, uint8_t v_fst_1215_, lean_object* v_as_1216_, size_t v_i_1217_, size_t v_stop_1218_, lean_object* v_b_1219_){
_start:
{
lean_object* v___y_1221_; uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_eq(v_i_1217_, v_stop_1218_);
if (v___x_1225_ == 0)
{
lean_object* v_snd_1226_; uint8_t v___x_1227_; 
v_snd_1226_ = lean_ctor_get(v_b_1219_, 1);
v___x_1227_ = lean_unbox(v_snd_1226_);
if (v___x_1227_ == 0)
{
v___y_1221_ = v_b_1219_;
goto v___jp_1220_;
}
else
{
lean_object* v_fst_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1245_; 
lean_inc(v_snd_1226_);
v_fst_1228_ = lean_ctor_get(v_b_1219_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_b_1219_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_b_1219_, 1);
lean_dec(v_unused_1246_);
v___x_1230_ = v_b_1219_;
v_isShared_1231_ = v_isSharedCheck_1245_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_fst_1228_);
lean_dec(v_b_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1245_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_fst_1232_ = lean_ctor_get(v_pivot_1213_, 0);
v_snd_1233_ = lean_ctor_get(v_pivot_1213_, 1);
v___x_1234_ = lean_array_uget_borrowed(v_as_1216_, v_i_1217_);
v___x_1235_ = lean_unbox(v_snd_1233_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1237_; 
lean_inc(v_fst_1232_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_fst_1232_);
v___x_1237_ = v___x_1230_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_fst_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_snd_1226_);
v___x_1237_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; 
lean_inc(v___x_1234_);
v___x_1238_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(v_n_1214_, v_fst_1228_, v___x_1237_, v___x_1234_);
lean_dec_ref(v___x_1237_);
v___y_1221_ = v___x_1238_;
goto v___jp_1220_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec(v_snd_1226_);
v___x_1240_ = lean_box(v_fst_1215_);
lean_inc(v_fst_1232_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1240_);
lean_ctor_set(v___x_1230_, 0, v_fst_1232_);
v___x_1242_ = v___x_1230_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_fst_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; 
lean_inc(v___x_1234_);
v___x_1243_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(v_n_1214_, v_fst_1228_, v___x_1242_, v___x_1234_);
lean_dec_ref(v___x_1242_);
v___y_1221_ = v___x_1243_;
goto v___jp_1220_;
}
}
}
}
}
else
{
return v_b_1219_;
}
v___jp_1220_:
{
size_t v___x_1222_; size_t v___x_1223_; 
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1217_, v___x_1222_);
v_i_1217_ = v___x_1223_;
v_b_1219_ = v___y_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1___boxed(lean_object* v_pivot_1247_, lean_object* v_n_1248_, lean_object* v_fst_1249_, lean_object* v_as_1250_, lean_object* v_i_1251_, lean_object* v_stop_1252_, lean_object* v_b_1253_){
_start:
{
uint8_t v_fst_535__boxed_1254_; size_t v_i_boxed_1255_; size_t v_stop_boxed_1256_; lean_object* v_res_1257_; 
v_fst_535__boxed_1254_ = lean_unbox(v_fst_1249_);
v_i_boxed_1255_ = lean_unbox_usize(v_i_1251_);
lean_dec(v_i_1251_);
v_stop_boxed_1256_ = lean_unbox_usize(v_stop_1252_);
lean_dec(v_stop_1252_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(v_pivot_1247_, v_n_1248_, v_fst_535__boxed_1254_, v_as_1250_, v_i_boxed_1255_, v_stop_boxed_1256_, v_b_1253_);
lean_dec_ref(v_as_1250_);
lean_dec(v_n_1248_);
lean_dec_ref(v_pivot_1247_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(uint8_t v___x_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
if (lean_obj_tag(v_a_1259_) == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = l_List_reverse___redArg(v_a_1260_);
return v___x_1261_;
}
else
{
lean_object* v_head_1262_; lean_object* v_tail_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1296_; 
v_head_1262_ = lean_ctor_get(v_a_1259_, 0);
v_tail_1263_ = lean_ctor_get(v_a_1259_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1259_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1265_ = v_a_1259_;
v_isShared_1266_ = v_isSharedCheck_1296_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_tail_1263_);
lean_inc(v_head_1262_);
lean_dec(v_a_1259_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1296_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___y_1268_; lean_object* v_snd_1273_; uint8_t v___x_1274_; 
v_snd_1273_ = lean_ctor_get(v_head_1262_, 1);
v___x_1274_ = lean_unbox(v_snd_1273_);
if (v___x_1274_ == 0)
{
lean_object* v_fst_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1283_; 
v_fst_1275_ = lean_ctor_get(v_head_1262_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_head_1262_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_head_1262_, 1);
lean_dec(v_unused_1284_);
v___x_1277_ = v_head_1262_;
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_fst_1275_);
lean_dec(v_head_1262_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1283_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1279_ = lean_box(v___x_1258_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1279_);
v___x_1281_ = v___x_1277_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_fst_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v___y_1268_ = v___x_1281_;
goto v___jp_1267_;
}
}
}
else
{
lean_object* v_fst_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1294_; 
v_fst_1285_ = lean_ctor_get(v_head_1262_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_head_1262_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v_head_1262_, 1);
lean_dec(v_unused_1295_);
v___x_1287_ = v_head_1262_;
v_isShared_1288_ = v_isSharedCheck_1294_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_fst_1285_);
lean_dec(v_head_1262_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1294_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = 0;
v___x_1290_ = lean_box(v___x_1289_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
v___y_1268_ = v___x_1292_;
goto v___jp_1267_;
}
}
}
v___jp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_a_1260_);
lean_ctor_set(v___x_1265_, 0, v___y_1268_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___y_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1260_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1259_ = v_tail_1263_;
v_a_1260_ = v___x_1270_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(lean_object* v___x_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
uint8_t v___x_588__boxed_1300_; lean_object* v_res_1301_; 
v___x_588__boxed_1300_ = lean_unbox(v___x_1297_);
v_res_1301_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v___x_588__boxed_1300_, v_a_1298_, v_a_1299_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object* v_n_1302_, lean_object* v_f_1303_, lean_object* v_c_1304_, lean_object* v_pivot_1305_, lean_object* v_rupHints_1306_, lean_object* v_ratHints_1307_){
_start:
{
uint8_t v___x_1308_; 
lean_inc_ref(v_ratHints_1307_);
lean_inc_ref(v_pivot_1305_);
v___x_1308_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(v_n_1302_, v_f_1303_, v_pivot_1305_, v_ratHints_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
lean_dec(v_c_1304_);
v___x_1309_ = lean_box(v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_f_1303_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v_negC_1312_; lean_object* v___x_1313_; lean_object* v_snd_1314_; uint8_t v___x_1315_; 
v___x_1311_ = lean_box(0);
lean_inc(v_c_1304_);
v_negC_1312_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v___x_1308_, v_c_1304_, v___x_1311_);
v___x_1313_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(v_n_1302_, v_f_1303_, v_negC_1312_);
v_snd_1314_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_snd_1314_);
v___x_1315_ = lean_unbox(v_snd_1314_);
if (v___x_1315_ == 0)
{
lean_object* v_fst_1316_; lean_object* v___x_1317_; lean_object* v_snd_1318_; lean_object* v_fst_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1390_; 
v_fst_1316_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_fst_1316_);
lean_dec_ref(v___x_1313_);
v___x_1317_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_1302_, v_fst_1316_, v_rupHints_1306_);
v_snd_1318_ = lean_ctor_get(v___x_1317_, 1);
v_fst_1319_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1321_ = v___x_1317_;
v_isShared_1322_ = v_isSharedCheck_1390_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snd_1318_);
lean_inc(v_fst_1319_);
lean_dec(v___x_1317_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1390_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1389_; 
v_fst_1323_ = lean_ctor_get(v_snd_1318_, 0);
v_snd_1324_ = lean_ctor_get(v_snd_1318_, 1);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_snd_1318_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1326_ = v_snd_1318_;
v_isShared_1327_ = v_isSharedCheck_1389_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snd_1324_);
lean_inc(v_fst_1323_);
lean_dec(v_snd_1318_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1389_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___y_1329_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1388_; 
v_fst_1348_ = lean_ctor_get(v_snd_1324_, 0);
v_snd_1349_ = lean_ctor_get(v_snd_1324_, 1);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_snd_1324_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1351_ = v_snd_1324_;
v_isShared_1352_ = v_isSharedCheck_1388_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_snd_1349_);
lean_inc(v_fst_1348_);
lean_dec(v_snd_1324_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1388_;
goto v_resetjp_1350_;
}
v___jp_1328_:
{
lean_object* v_clauses_1330_; lean_object* v_rupUnits_1331_; lean_object* v_ratUnits_1332_; lean_object* v_assignments_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1347_; 
v_clauses_1330_ = lean_ctor_get(v___y_1329_, 0);
v_rupUnits_1331_ = lean_ctor_get(v___y_1329_, 1);
v_ratUnits_1332_ = lean_ctor_get(v___y_1329_, 2);
v_assignments_1333_ = lean_ctor_get(v___y_1329_, 3);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___y_1329_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1335_ = v___y_1329_;
v_isShared_1336_ = v_isSharedCheck_1347_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_assignments_1333_);
lean_inc(v_ratUnits_1332_);
lean_inc(v_rupUnits_1331_);
lean_inc(v_clauses_1330_);
lean_dec(v___y_1329_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1347_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_assignments_1337_; lean_object* v___x_1339_; 
v_assignments_1337_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_1333_, v_fst_1323_);
lean_dec(v_fst_1323_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 3, v_assignments_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_clauses_1330_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_rupUnits_1331_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_ratUnits_1332_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_assignments_1337_);
v___x_1339_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v_f_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v_f_1340_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_1302_, v___x_1339_);
v___x_1341_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_1340_, v_c_1304_);
v___x_1342_ = lean_box(v___x_1308_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1342_);
lean_ctor_set(v___x_1326_, 0, v___x_1341_);
v___x_1344_ = v___x_1326_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
v_resetjp_1350_:
{
lean_object* v_fst_1354_; uint8_t v_snd_1355_; lean_object* v___y_1360_; uint8_t v___x_1364_; 
v___x_1364_ = lean_unbox(v_snd_1349_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
lean_dec(v_snd_1314_);
v___x_1365_ = lean_unbox(v_fst_1348_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
lean_dec(v_snd_1349_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_get_size(v_ratHints_1307_);
v___x_1368_ = lean_nat_dec_lt(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_del_object(v___x_1321_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
v_fst_1354_ = v_fst_1319_;
v_snd_1355_ = v___x_1308_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_box(v___x_1308_);
lean_inc(v_fst_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1369_);
v___x_1371_ = v___x_1321_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_fst_1319_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_nat_dec_le(v___x_1367_, v___x_1367_);
if (v___x_1372_ == 0)
{
if (v___x_1368_ == 0)
{
lean_dec_ref(v___x_1371_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
v_fst_1354_ = v_fst_1319_;
v_snd_1355_ = v___x_1308_;
goto v___jp_1353_;
}
else
{
size_t v___x_1373_; size_t v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_fst_1319_);
v___x_1373_ = ((size_t)0ULL);
v___x_1374_ = lean_usize_of_nat(v___x_1367_);
v___x_1375_ = lean_unbox(v_fst_1348_);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(v_pivot_1305_, v_n_1302_, v___x_1375_, v_ratHints_1307_, v___x_1373_, v___x_1374_, v___x_1371_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
v___y_1360_ = v___x_1376_;
goto v___jp_1359_;
}
}
else
{
size_t v___x_1377_; size_t v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_fst_1319_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_of_nat(v___x_1367_);
v___x_1379_ = lean_unbox(v_fst_1348_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(v_pivot_1305_, v_n_1302_, v___x_1379_, v_ratHints_1307_, v___x_1377_, v___x_1378_, v___x_1371_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
v___y_1360_ = v___x_1380_;
goto v___jp_1359_;
}
}
}
}
else
{
lean_object* v___x_1383_; 
lean_del_object(v___x_1351_);
lean_dec(v_fst_1348_);
lean_del_object(v___x_1326_);
lean_dec(v_fst_1323_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
lean_dec(v_c_1304_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v_snd_1349_);
v___x_1383_ = v___x_1321_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_fst_1319_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_snd_1349_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_object* v___x_1386_; 
lean_del_object(v___x_1351_);
lean_dec(v_snd_1349_);
lean_dec(v_fst_1348_);
lean_del_object(v___x_1326_);
lean_dec(v_fst_1323_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
lean_dec(v_c_1304_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v_snd_1314_);
v___x_1386_ = v___x_1321_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_fst_1319_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_snd_1314_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
v___jp_1353_:
{
if (v_snd_1355_ == 0)
{
if (v___x_1308_ == 0)
{
lean_del_object(v___x_1351_);
lean_dec(v_fst_1348_);
v___y_1329_ = v_fst_1354_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1357_; 
lean_del_object(v___x_1326_);
lean_dec(v_fst_1323_);
lean_dec(v_c_1304_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 1, v_fst_1348_);
lean_ctor_set(v___x_1351_, 0, v_fst_1354_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_fst_1354_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_fst_1348_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_del_object(v___x_1351_);
lean_dec(v_fst_1348_);
v___y_1329_ = v_fst_1354_;
goto v___jp_1328_;
}
}
v___jp_1359_:
{
lean_object* v_fst_1361_; lean_object* v_snd_1362_; uint8_t v___x_1363_; 
v_fst_1361_ = lean_ctor_get(v___y_1360_, 0);
lean_inc(v_fst_1361_);
v_snd_1362_ = lean_ctor_get(v___y_1360_, 1);
lean_inc(v_snd_1362_);
lean_dec_ref(v___y_1360_);
v___x_1363_ = lean_unbox(v_snd_1362_);
lean_dec(v_snd_1362_);
v_fst_1354_ = v_fst_1361_;
v_snd_1355_ = v___x_1363_;
goto v___jp_1353_;
}
}
}
}
}
else
{
lean_object* v_fst_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1400_; 
lean_dec(v_snd_1314_);
lean_dec_ref(v_ratHints_1307_);
lean_dec_ref(v_pivot_1305_);
lean_dec(v_c_1304_);
v_fst_1391_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1313_, 1);
lean_dec(v_unused_1401_);
v___x_1393_ = v___x_1313_;
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_fst_1391_);
lean_dec(v___x_1313_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1400_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = 0;
v___x_1396_ = lean_box(v___x_1395_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 1, v___x_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_fst_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(lean_object* v_n_1402_, lean_object* v_f_1403_, lean_object* v_c_1404_, lean_object* v_pivot_1405_, lean_object* v_rupHints_1406_, lean_object* v_ratHints_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_1402_, v_f_1403_, v_c_1404_, v_pivot_1405_, v_rupHints_1406_, v_ratHints_1407_);
lean_dec_ref(v_rupHints_1406_);
lean_dec(v_n_1402_);
return v_res_1408_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
if (lean_obj_tag(v_x_1410_) == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = 1;
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; 
v___x_1412_ = 0;
return v___x_1412_;
}
}
else
{
if (lean_obj_tag(v_x_1410_) == 0)
{
uint8_t v___x_1413_; 
v___x_1413_ = 0;
return v___x_1413_;
}
else
{
lean_object* v_val_1414_; lean_object* v_val_1415_; uint8_t v___x_1416_; 
v_val_1414_ = lean_ctor_get(v_x_1409_, 0);
v_val_1415_ = lean_ctor_get(v_x_1410_, 0);
v___x_1416_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_val_1414_, v_val_1415_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg___boxed(lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_x_1417_, v_x_1418_);
lean_dec(v_x_1418_);
lean_dec(v_x_1417_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(lean_object* v_n_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_x_1422_, v_x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___boxed(lean_object* v_n_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(v_n_1425_, v_x_1426_, v_x_1427_);
lean_dec(v_x_1427_);
lean_dec(v_x_1426_);
lean_dec(v_n_1425_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(lean_object* v_n_1430_, lean_object* v_as_1431_, size_t v_sz_1432_, size_t v_i_1433_, lean_object* v_b_1434_){
_start:
{
lean_object* v_a_1436_; uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_lt(v_i_1433_, v_sz_1432_);
if (v___x_1440_ == 0)
{
return v_b_1434_;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v_a_1441_ = lean_array_uget_borrowed(v_as_1431_, v_i_1433_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_a_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_nat_add(v_b_1434_, v___x_1444_);
lean_dec(v_b_1434_);
v_a_1436_ = v___x_1445_;
goto v___jp_1435_;
}
else
{
v_a_1436_ = v_b_1434_;
goto v___jp_1435_;
}
}
v___jp_1435_:
{
size_t v___x_1437_; size_t v___x_1438_; 
v___x_1437_ = ((size_t)1ULL);
v___x_1438_ = lean_usize_add(v_i_1433_, v___x_1437_);
v_i_1433_ = v___x_1438_;
v_b_1434_ = v_a_1436_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1___boxed(lean_object* v_n_1446_, lean_object* v_as_1447_, lean_object* v_sz_1448_, lean_object* v_i_1449_, lean_object* v_b_1450_){
_start:
{
size_t v_sz_boxed_1451_; size_t v_i_boxed_1452_; lean_object* v_res_1453_; 
v_sz_boxed_1451_ = lean_unbox_usize(v_sz_1448_);
lean_dec(v_sz_1448_);
v_i_boxed_1452_ = lean_unbox_usize(v_i_1449_);
lean_dec(v_i_1449_);
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(v_n_1446_, v_as_1447_, v_sz_boxed_1451_, v_i_boxed_1452_, v_b_1450_);
lean_dec_ref(v_as_1447_);
lean_dec(v_n_1446_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(lean_object* v_n_1454_, lean_object* v_f_1455_){
_start:
{
lean_object* v_clauses_1456_; lean_object* v_numClauses_1457_; size_t v_sz_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v_clauses_1456_ = lean_ctor_get(v_f_1455_, 0);
v_numClauses_1457_ = lean_unsigned_to_nat(0u);
v_sz_1458_ = lean_array_size(v_clauses_1456_);
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(v_n_1454_, v_clauses_1456_, v_sz_1458_, v___x_1459_, v_numClauses_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula___boxed(lean_object* v_n_1461_, lean_object* v_f_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(v_n_1461_, v_f_1462_);
lean_dec_ref(v_f_1462_);
lean_dec(v_n_1461_);
return v_res_1463_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
}
#ifdef __cplusplus
}
#endif
