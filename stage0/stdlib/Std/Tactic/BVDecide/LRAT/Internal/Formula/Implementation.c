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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_snd_326_; lean_object* v_fst_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_376_; 
v_snd_326_ = lean_ctor_get(v_x_324_, 1);
lean_inc(v_snd_326_);
v_fst_327_ = lean_ctor_get(v_x_324_, 0);
v_fst_328_ = lean_ctor_get(v_snd_326_, 0);
v_snd_329_ = lean_ctor_get(v_snd_326_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_snd_326_);
if (v_isSharedCheck_376_ == 0)
{
v___x_331_ = v_snd_326_;
v_isShared_332_ = v_isSharedCheck_376_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_snd_329_);
lean_inc(v_fst_328_);
lean_dec(v_snd_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_376_;
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
lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_373_; 
lean_inc(v_fst_327_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_x_324_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_x_324_, 0);
lean_dec(v_unused_375_);
v___x_342_ = v_x_324_;
v_isShared_343_ = v_isSharedCheck_373_;
goto v_resetjp_341_;
}
else
{
lean_dec(v_x_324_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_373_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___x_344_; lean_object* v_units_345_; lean_object* v___y_347_; uint8_t v___y_348_; lean_object* v___y_357_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_344_ = 1;
v_units_345_ = lean_array_push(v_fst_327_, v_x_325_);
v___x_363_ = lean_array_get_size(v_fst_328_);
v___x_364_ = lean_nat_dec_lt(v_fst_333_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec(v_snd_334_);
lean_dec(v_fst_333_);
v___y_357_ = v_fst_328_;
goto v___jp_356_;
}
else
{
lean_object* v_v_365_; lean_object* v___x_366_; lean_object* v_xs_x27_367_; uint8_t v___x_368_; uint8_t v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_v_365_ = lean_array_fget(v_fst_328_, v_fst_333_);
v___x_366_ = lean_box(0);
v_xs_x27_367_ = lean_array_fset(v_fst_328_, v_fst_333_, v___x_366_);
v___x_368_ = lean_unbox(v_snd_334_);
lean_dec(v_snd_334_);
v___x_369_ = lean_unbox(v_v_365_);
lean_dec(v_v_365_);
v___x_370_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v___x_368_, v___x_369_);
v___x_371_ = lean_box(v___x_370_);
v___x_372_ = lean_array_fset(v_xs_x27_367_, v_fst_333_, v___x_371_);
lean_dec(v_fst_333_);
v___y_357_ = v___x_372_;
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
uint8_t v___x_359_; uint8_t v___x_360_; uint8_t v___x_361_; uint8_t v___x_362_; 
v___x_359_ = 3;
v___x_360_ = lean_unbox(v_curAssignment_337_);
lean_dec(v_curAssignment_337_);
v___x_361_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(v___x_360_, v___x_359_);
v___x_362_ = lean_bool_not(v___x_361_);
v___y_347_ = v___y_357_;
v___y_348_ = v___x_362_;
goto v___jp_346_;
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(lean_object* v_n_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(v_x_378_, v_x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___boxed(lean_object* v_n_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(v_n_381_, v_x_382_, v_x_383_);
lean_dec(v_n_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
return v_x_385_;
}
else
{
lean_object* v_head_387_; lean_object* v_tail_388_; lean_object* v___x_389_; 
v_head_387_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_head_387_);
v_tail_388_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_tail_388_);
lean_dec_ref_known(v_x_386_, 2);
v___x_389_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(v_x_385_, v_head_387_);
v_x_385_ = v___x_389_;
v_x_386_ = v_tail_388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(lean_object* v_n_391_, lean_object* v_f_392_, lean_object* v_ls_393_){
_start:
{
lean_object* v_clauses_394_; lean_object* v_rupUnits_395_; lean_object* v_ratUnits_396_; lean_object* v_assignments_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_420_; 
v_clauses_394_ = lean_ctor_get(v_f_392_, 0);
v_rupUnits_395_ = lean_ctor_get(v_f_392_, 1);
v_ratUnits_396_ = lean_ctor_get(v_f_392_, 2);
v_assignments_397_ = lean_ctor_get(v_f_392_, 3);
v_isSharedCheck_420_ = !lean_is_exclusive(v_f_392_);
if (v_isSharedCheck_420_ == 0)
{
v___x_399_ = v_f_392_;
v_isShared_400_ = v_isSharedCheck_420_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_assignments_397_);
lean_inc(v_ratUnits_396_);
lean_inc(v_rupUnits_395_);
lean_inc(v_clauses_394_);
lean_dec(v_f_392_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_420_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_snd_406_; lean_object* v_fst_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_419_; 
v___x_401_ = 0;
v___x_402_ = lean_box(v___x_401_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_assignments_397_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_rupUnits_395_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v___x_404_, v_ls_393_);
v_snd_406_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_snd_406_);
v_fst_407_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_fst_407_);
lean_dec_ref(v___x_405_);
v_fst_408_ = lean_ctor_get(v_snd_406_, 0);
v_snd_409_ = lean_ctor_get(v_snd_406_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_snd_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_411_ = v_snd_406_;
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_snd_409_);
lean_inc(v_fst_408_);
lean_dec(v_snd_406_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 3, v_fst_408_);
lean_ctor_set(v___x_399_, 1, v_fst_407_);
v___x_414_ = v___x_399_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_clauses_394_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_fst_407_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_ratUnits_396_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_fst_408_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_416_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_snd_409_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits___boxed(lean_object* v_n_421_, lean_object* v_f_422_, lean_object* v_ls_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(v_n_421_, v_f_422_, v_ls_423_);
lean_dec(v_n_421_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(lean_object* v_n_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v_x_426_, v_x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___boxed(lean_object* v_n_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(v_n_429_, v_x_430_, v_x_431_);
lean_dec(v_n_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(lean_object* v_f_433_, lean_object* v_ls_434_){
_start:
{
lean_object* v_clauses_435_; lean_object* v_rupUnits_436_; lean_object* v_ratUnits_437_; lean_object* v_assignments_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_461_; 
v_clauses_435_ = lean_ctor_get(v_f_433_, 0);
v_rupUnits_436_ = lean_ctor_get(v_f_433_, 1);
v_ratUnits_437_ = lean_ctor_get(v_f_433_, 2);
v_assignments_438_ = lean_ctor_get(v_f_433_, 3);
v_isSharedCheck_461_ = !lean_is_exclusive(v_f_433_);
if (v_isSharedCheck_461_ == 0)
{
v___x_440_ = v_f_433_;
v_isShared_441_ = v_isSharedCheck_461_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_assignments_438_);
lean_inc(v_ratUnits_437_);
lean_inc(v_rupUnits_436_);
lean_inc(v_clauses_435_);
lean_dec(v_f_433_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_461_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_snd_447_; lean_object* v_fst_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_460_; 
v___x_442_ = 0;
v___x_443_ = lean_box(v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_assignments_438_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_ratUnits_437_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v___x_445_, v_ls_434_);
v_snd_447_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_447_);
v_fst_448_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_448_);
lean_dec_ref(v___x_446_);
v_fst_449_ = lean_ctor_get(v_snd_447_, 0);
v_snd_450_ = lean_ctor_get(v_snd_447_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v_snd_447_);
if (v_isSharedCheck_460_ == 0)
{
v___x_452_ = v_snd_447_;
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
lean_dec(v_snd_447_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 3, v_fst_449_);
lean_ctor_set(v___x_440_, 2, v_fst_448_);
v___x_455_ = v___x_440_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_clauses_435_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_rupUnits_436_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_fst_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_fst_449_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_455_);
v___x_457_ = v___x_452_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_snd_450_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(lean_object* v_n_462_, lean_object* v_f_463_, lean_object* v_ls_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(v_f_463_, v_ls_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___boxed(lean_object* v_n_466_, lean_object* v_f_467_, lean_object* v_ls_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(v_n_466_, v_f_467_, v_ls_468_);
lean_dec(v_n_466_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_fst_472_ = lean_ctor_get(v_x_471_, 0);
v_snd_473_ = lean_ctor_get(v_x_471_, 1);
v___x_474_ = lean_array_get_size(v_x_470_);
v___x_475_ = lean_nat_dec_lt(v_fst_472_, v___x_474_);
if (v___x_475_ == 0)
{
return v_x_470_;
}
else
{
lean_object* v_v_476_; lean_object* v___x_477_; lean_object* v_xs_x27_478_; uint8_t v___x_479_; uint8_t v___x_480_; uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_v_476_ = lean_array_fget(v_x_470_, v_fst_472_);
v___x_477_ = lean_box(0);
v_xs_x27_478_ = lean_array_fset(v_x_470_, v_fst_472_, v___x_477_);
v___x_479_ = lean_unbox(v_snd_473_);
v___x_480_ = lean_unbox(v_v_476_);
lean_dec(v_v_476_);
v___x_481_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(v___x_479_, v___x_480_);
v___x_482_ = lean_box(v___x_481_);
v___x_483_ = lean_array_fset(v_xs_x27_478_, v_fst_472_, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg___boxed(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_484_, v_x_485_);
lean_dec_ref(v_x_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(lean_object* v_n_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___boxed(lean_object* v_n_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(v_n_491_, v_x_492_, v_x_493_);
lean_dec_ref(v_x_493_);
lean_dec(v_n_491_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; size_t v___x_502_; size_t v___x_503_; 
v___x_500_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
v___x_501_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_b_498_, v___x_500_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_496_, v___x_502_);
v_i_496_ = v___x_503_;
v_b_498_ = v___x_501_;
goto _start;
}
else
{
return v_b_498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg___boxed(lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_stop_507_, lean_object* v_b_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; lean_object* v_res_511_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_507_);
lean_dec(v_stop_507_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_as_505_, v_i_boxed_509_, v_stop_boxed_510_, v_b_508_);
lean_dec_ref(v_as_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(lean_object* v_n_512_, lean_object* v_f_513_){
_start:
{
lean_object* v_clauses_514_; lean_object* v_rupUnits_515_; lean_object* v_ratUnits_516_; lean_object* v_assignments_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_537_; 
v_clauses_514_ = lean_ctor_get(v_f_513_, 0);
v_rupUnits_515_ = lean_ctor_get(v_f_513_, 1);
v_ratUnits_516_ = lean_ctor_get(v_f_513_, 2);
v_assignments_517_ = lean_ctor_get(v_f_513_, 3);
v_isSharedCheck_537_ = !lean_is_exclusive(v_f_513_);
if (v_isSharedCheck_537_ == 0)
{
v___x_519_ = v_f_513_;
v_isShared_520_ = v_isSharedCheck_537_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_assignments_517_);
lean_inc(v_ratUnits_516_);
lean_inc(v_rupUnits_515_);
lean_inc(v_clauses_514_);
lean_dec(v_f_513_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_537_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___y_522_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_array_get_size(v_rupUnits_515_);
v___x_529_ = lean_nat_dec_lt(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec_ref(v_rupUnits_515_);
v___y_522_ = v_assignments_517_;
goto v___jp_521_;
}
else
{
uint8_t v___x_530_; 
v___x_530_ = lean_nat_dec_le(v___x_528_, v___x_528_);
if (v___x_530_ == 0)
{
if (v___x_529_ == 0)
{
lean_dec_ref(v_rupUnits_515_);
v___y_522_ = v_assignments_517_;
goto v___jp_521_;
}
else
{
size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((size_t)0ULL);
v___x_532_ = lean_usize_of_nat(v___x_528_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_rupUnits_515_, v___x_531_, v___x_532_, v_assignments_517_);
lean_dec_ref(v_rupUnits_515_);
v___y_522_ = v___x_533_;
goto v___jp_521_;
}
}
else
{
size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((size_t)0ULL);
v___x_535_ = lean_usize_of_nat(v___x_528_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_rupUnits_515_, v___x_534_, v___x_535_, v_assignments_517_);
lean_dec_ref(v_rupUnits_515_);
v___y_522_ = v___x_536_;
goto v___jp_521_;
}
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 3, v___y_522_);
lean_ctor_set(v___x_519_, 1, v___x_523_);
v___x_525_ = v___x_519_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_clauses_514_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_ratUnits_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v___y_522_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits___boxed(lean_object* v_n_538_, lean_object* v_f_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_538_, v_f_539_);
lean_dec(v_n_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(lean_object* v_n_541_, lean_object* v_as_542_, size_t v_i_543_, size_t v_stop_544_, lean_object* v_b_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_as_542_, v_i_543_, v_stop_544_, v_b_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___boxed(lean_object* v_n_547_, lean_object* v_as_548_, lean_object* v_i_549_, lean_object* v_stop_550_, lean_object* v_b_551_){
_start:
{
size_t v_i_boxed_552_; size_t v_stop_boxed_553_; lean_object* v_res_554_; 
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_stop_boxed_553_ = lean_unbox_usize(v_stop_550_);
lean_dec(v_stop_550_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(v_n_547_, v_as_548_, v_i_boxed_552_, v_stop_boxed_553_, v_b_551_);
lean_dec_ref(v_as_548_);
lean_dec(v_n_547_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(lean_object* v_f_555_){
_start:
{
lean_object* v_clauses_556_; lean_object* v_rupUnits_557_; lean_object* v_ratUnits_558_; lean_object* v_assignments_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_579_; 
v_clauses_556_ = lean_ctor_get(v_f_555_, 0);
v_rupUnits_557_ = lean_ctor_get(v_f_555_, 1);
v_ratUnits_558_ = lean_ctor_get(v_f_555_, 2);
v_assignments_559_ = lean_ctor_get(v_f_555_, 3);
v_isSharedCheck_579_ = !lean_is_exclusive(v_f_555_);
if (v_isSharedCheck_579_ == 0)
{
v___x_561_ = v_f_555_;
v_isShared_562_ = v_isSharedCheck_579_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_assignments_559_);
lean_inc(v_ratUnits_558_);
lean_inc(v_rupUnits_557_);
lean_inc(v_clauses_556_);
lean_dec(v_f_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_579_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___y_564_; lean_object* v___x_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_array_get_size(v_ratUnits_558_);
v___x_571_ = lean_nat_dec_lt(v___x_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_dec_ref(v_ratUnits_558_);
v___y_564_ = v_assignments_559_;
goto v___jp_563_;
}
else
{
uint8_t v___x_572_; 
v___x_572_ = lean_nat_dec_le(v___x_570_, v___x_570_);
if (v___x_572_ == 0)
{
if (v___x_571_ == 0)
{
lean_dec_ref(v_ratUnits_558_);
v___y_564_ = v_assignments_559_;
goto v___jp_563_;
}
else
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v___x_573_ = ((size_t)0ULL);
v___x_574_ = lean_usize_of_nat(v___x_570_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_ratUnits_558_, v___x_573_, v___x_574_, v_assignments_559_);
lean_dec_ref(v_ratUnits_558_);
v___y_564_ = v___x_575_;
goto v___jp_563_;
}
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_570_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_ratUnits_558_, v___x_576_, v___x_577_, v_assignments_559_);
lean_dec_ref(v_ratUnits_558_);
v___y_564_ = v___x_578_;
goto v___jp_563_;
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 3, v___y_564_);
lean_ctor_set(v___x_561_, 2, v___x_565_);
v___x_567_ = v___x_561_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_clauses_556_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_rupUnits_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v___y_564_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(lean_object* v_n_580_, lean_object* v_f_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v_f_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___boxed(lean_object* v_n_583_, lean_object* v_f_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(v_n_583_, v_f_584_);
lean_dec(v_n_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
if (lean_obj_tag(v_x_587_) == 0)
{
return v_x_586_;
}
else
{
lean_object* v_head_588_; lean_object* v_tail_589_; lean_object* v___x_590_; 
v_head_588_ = lean_ctor_get(v_x_587_, 0);
v_tail_589_ = lean_ctor_get(v_x_587_, 1);
v___x_590_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_586_, v_head_588_);
v_x_586_ = v___x_590_;
v_x_587_ = v_tail_589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg___boxed(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_x_592_, v_x_593_);
lean_dec(v_x_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(lean_object* v_n_595_, lean_object* v_assignments_596_, lean_object* v_derivedLits_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_596_, v_derivedLits_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments___boxed(lean_object* v_n_599_, lean_object* v_assignments_600_, lean_object* v_derivedLits_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(v_n_599_, v_assignments_600_, v_derivedLits_601_);
lean_dec(v_derivedLits_601_);
lean_dec(v_n_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(lean_object* v_n_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_x_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___boxed(lean_object* v_n_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(v_n_607_, v_x_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec(v_n_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(lean_object* v_n_611_, lean_object* v_clauses_612_, lean_object* v_x_613_, lean_object* v_id_614_){
_start:
{
lean_object* v_snd_615_; lean_object* v_snd_616_; lean_object* v_snd_617_; uint8_t v___x_618_; 
v_snd_615_ = lean_ctor_get(v_x_613_, 1);
lean_inc(v_snd_615_);
v_snd_616_ = lean_ctor_get(v_snd_615_, 1);
lean_inc(v_snd_616_);
v_snd_617_ = lean_ctor_get(v_snd_616_, 1);
v___x_618_ = lean_unbox(v_snd_617_);
if (v___x_618_ == 0)
{
lean_object* v_fst_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_699_; 
v_fst_619_ = lean_ctor_get(v_snd_616_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_snd_616_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_snd_616_, 1);
lean_dec(v_unused_700_);
v___x_621_ = v_snd_616_;
v_isShared_622_ = v_isSharedCheck_699_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_fst_619_);
lean_dec(v_snd_616_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_699_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; 
v___x_623_ = lean_unbox(v_fst_619_);
if (v___x_623_ == 0)
{
lean_object* v_fst_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_697_; 
v_fst_624_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_x_613_, 1);
lean_dec(v_unused_698_);
v___x_626_ = v_x_613_;
v_isShared_627_ = v_isSharedCheck_697_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_fst_624_);
lean_dec(v_x_613_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_697_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_fst_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_695_; 
v_fst_628_ = lean_ctor_get(v_snd_615_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_snd_615_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_snd_615_, 1);
lean_dec(v_unused_696_);
v___x_630_ = v_snd_615_;
v_isShared_631_ = v_isSharedCheck_695_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_fst_628_);
lean_dec(v_snd_615_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_695_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_632_ = 1;
v___x_644_ = lean_array_get_size(v_clauses_612_);
v___x_645_ = lean_nat_dec_lt(v_id_614_, v___x_644_);
if (v___x_645_ == 0)
{
goto v___jp_633_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_fget_borrowed(v_clauses_612_, v_id_614_);
if (lean_obj_tag(v___x_646_) == 0)
{
goto v___jp_633_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_648_; 
lean_del_object(v___x_630_);
lean_del_object(v___x_626_);
lean_del_object(v___x_621_);
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
v___x_648_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(v_n_611_, v_val_647_, v_fst_624_);
switch(lean_obj_tag(v___x_648_))
{
case 2:
{
lean_object* v_l_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; lean_object* v___y_659_; 
v_l_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_l_649_);
lean_dec_ref_known(v___x_648_, 1);
v_fst_650_ = lean_ctor_get(v_l_649_, 0);
v_snd_651_ = lean_ctor_get(v_l_649_, 1);
v___x_652_ = 0;
v___x_653_ = lean_box(v___x_652_);
v___x_654_ = lean_array_get(v___x_653_, v_fst_624_, v_fst_650_);
lean_dec(v___x_653_);
v___x_655_ = lean_unbox(v_snd_651_);
v___x_656_ = lean_unbox(v___x_654_);
lean_dec(v___x_654_);
v___x_657_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
lean_dec(v_fst_619_);
v___x_666_ = lean_array_get_size(v_fst_624_);
v___x_667_ = lean_nat_dec_lt(v_fst_650_, v___x_666_);
if (v___x_667_ == 0)
{
v___y_659_ = v_fst_624_;
goto v___jp_658_;
}
else
{
lean_object* v_v_668_; lean_object* v___x_669_; lean_object* v_xs_x27_670_; uint8_t v___x_671_; uint8_t v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_v_668_ = lean_array_fget(v_fst_624_, v_fst_650_);
v___x_669_ = lean_box(0);
v_xs_x27_670_ = lean_array_fset(v_fst_624_, v_fst_650_, v___x_669_);
v___x_671_ = lean_unbox(v_snd_651_);
v___x_672_ = lean_unbox(v_v_668_);
lean_dec(v_v_668_);
v___x_673_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v___x_671_, v___x_672_);
v___x_674_ = lean_box(v___x_673_);
v___x_675_ = lean_array_fset(v_xs_x27_670_, v_fst_650_, v___x_674_);
v___y_659_ = v___x_675_;
goto v___jp_658_;
}
}
else
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_684_; 
v_isSharedCheck_684_ = !lean_is_exclusive(v_l_649_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; 
v_unused_685_ = lean_ctor_get(v_l_649_, 1);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_l_649_, 0);
lean_dec(v_unused_686_);
v___x_677_ = v_l_649_;
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_l_649_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_684_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
lean_inc(v_fst_619_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v_fst_619_);
lean_ctor_set(v___x_677_, 0, v_fst_619_);
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_fst_619_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_fst_619_);
v___x_680_ = v_reuseFailAlloc_683_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_fst_628_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_fst_624_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
return v___x_682_;
}
}
}
v___jp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v_l_649_);
lean_ctor_set(v___x_660_, 1, v_fst_628_);
v___x_661_ = lean_box(v___x_657_);
v___x_662_ = lean_box(v___x_657_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_660_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_659_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
return v___x_665_;
}
}
case 3:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_687_ = lean_box(v___x_632_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v_fst_619_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v_fst_628_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v_fst_624_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
return v___x_690_;
}
default: 
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_648_);
v___x_691_ = lean_box(v___x_632_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_fst_619_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_fst_628_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v_fst_624_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
return v___x_694_;
}
}
}
}
v___jp_633_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_box(v___x_632_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_634_);
v___x_636_ = v___x_621_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fst_619_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_634_);
v___x_636_ = v_reuseFailAlloc_643_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_636_);
v___x_638_ = v___x_630_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_fst_628_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_642_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 1, v___x_638_);
v___x_640_ = v___x_626_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_fst_624_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_621_);
lean_dec(v_fst_619_);
lean_dec(v_snd_615_);
return v_x_613_;
}
}
}
else
{
lean_dec(v_snd_616_);
lean_dec(v_snd_615_);
return v_x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint___boxed(lean_object* v_n_701_, lean_object* v_clauses_702_, lean_object* v_x_703_, lean_object* v_id_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(v_n_701_, v_clauses_702_, v_x_703_, v_id_704_);
lean_dec(v_id_704_);
lean_dec_ref(v_clauses_702_);
lean_dec(v_n_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(lean_object* v_n_706_, lean_object* v_clauses_707_, lean_object* v_as_708_, size_t v_i_709_, size_t v_stop_710_, lean_object* v_b_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_eq(v_i_709_, v_stop_710_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; size_t v___x_715_; size_t v___x_716_; 
v___x_713_ = lean_array_uget_borrowed(v_as_708_, v_i_709_);
v___x_714_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(v_n_706_, v_clauses_707_, v_b_711_, v___x_713_);
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_add(v_i_709_, v___x_715_);
v_i_709_ = v___x_716_;
v_b_711_ = v___x_714_;
goto _start;
}
else
{
return v_b_711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0___boxed(lean_object* v_n_718_, lean_object* v_clauses_719_, lean_object* v_as_720_, lean_object* v_i_721_, lean_object* v_stop_722_, lean_object* v_b_723_){
_start:
{
size_t v_i_boxed_724_; size_t v_stop_boxed_725_; lean_object* v_res_726_; 
v_i_boxed_724_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_stop_boxed_725_ = lean_unbox_usize(v_stop_722_);
lean_dec(v_stop_722_);
v_res_726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_718_, v_clauses_719_, v_as_720_, v_i_boxed_724_, v_stop_boxed_725_, v_b_723_);
lean_dec_ref(v_as_720_);
lean_dec_ref(v_clauses_719_);
lean_dec(v_n_718_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(lean_object* v_n_734_, lean_object* v_f_735_, lean_object* v_rupHints_736_){
_start:
{
lean_object* v_clauses_737_; lean_object* v_rupUnits_738_; lean_object* v_ratUnits_739_; lean_object* v_assignments_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_767_; 
v_clauses_737_ = lean_ctor_get(v_f_735_, 0);
v_rupUnits_738_ = lean_ctor_get(v_f_735_, 1);
v_ratUnits_739_ = lean_ctor_get(v_f_735_, 2);
v_assignments_740_ = lean_ctor_get(v_f_735_, 3);
v_isSharedCheck_767_ = !lean_is_exclusive(v_f_735_);
if (v_isSharedCheck_767_ == 0)
{
v___x_742_ = v_f_735_;
v_isShared_743_ = v_isSharedCheck_767_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_assignments_740_);
lean_inc(v_ratUnits_739_);
lean_inc(v_rupUnits_738_);
lean_inc(v_clauses_737_);
lean_dec(v_f_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_767_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_fst_745_; lean_object* v_snd_746_; lean_object* v___y_752_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_755_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1));
v___x_756_ = lean_unsigned_to_nat(0u);
v___x_757_ = lean_array_get_size(v_rupHints_736_);
v___x_758_ = lean_nat_dec_lt(v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
v_fst_745_ = v_assignments_740_;
v_snd_746_ = v___x_755_;
goto v___jp_744_;
}
else
{
lean_object* v___x_759_; uint8_t v___x_760_; 
lean_inc_ref(v_assignments_740_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_assignments_740_);
lean_ctor_set(v___x_759_, 1, v___x_755_);
v___x_760_ = lean_nat_dec_le(v___x_757_, v___x_757_);
if (v___x_760_ == 0)
{
if (v___x_758_ == 0)
{
lean_dec_ref_known(v___x_759_, 2);
v_fst_745_ = v_assignments_740_;
v_snd_746_ = v___x_755_;
goto v___jp_744_;
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
lean_dec_ref(v_assignments_740_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_757_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_734_, v_clauses_737_, v_rupHints_736_, v___x_761_, v___x_762_, v___x_759_);
v___y_752_ = v___x_763_;
goto v___jp_751_;
}
}
else
{
size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
lean_dec_ref(v_assignments_740_);
v___x_764_ = ((size_t)0ULL);
v___x_765_ = lean_usize_of_nat(v___x_757_);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_734_, v_clauses_737_, v_rupHints_736_, v___x_764_, v___x_765_, v___x_759_);
v___y_752_ = v___x_766_;
goto v___jp_751_;
}
}
v___jp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v_fst_745_);
v___x_748_ = v___x_742_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_clauses_737_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_rupUnits_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_ratUnits_739_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_fst_745_);
v___x_748_ = v_reuseFailAlloc_750_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_snd_746_);
return v___x_749_;
}
}
v___jp_751_:
{
lean_object* v_fst_753_; lean_object* v_snd_754_; 
v_fst_753_ = lean_ctor_get(v___y_752_, 0);
lean_inc(v_fst_753_);
v_snd_754_ = lean_ctor_get(v___y_752_, 1);
lean_inc(v_snd_754_);
lean_dec_ref(v___y_752_);
v_fst_745_ = v_fst_753_;
v_snd_746_ = v_snd_754_;
goto v___jp_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___boxed(lean_object* v_n_768_, lean_object* v_f_769_, lean_object* v_rupHints_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_768_, v_f_769_, v_rupHints_770_);
lean_dec_ref(v_rupHints_770_);
lean_dec(v_n_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
if (lean_obj_tag(v_a_772_) == 0)
{
lean_object* v___x_774_; 
v___x_774_ = l_List_reverse___redArg(v_a_773_);
return v___x_774_;
}
else
{
lean_object* v_head_775_; lean_object* v_tail_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_796_; 
v_head_775_ = lean_ctor_get(v_a_772_, 0);
v_tail_776_ = lean_ctor_get(v_a_772_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_a_772_);
if (v_isSharedCheck_796_ == 0)
{
v___x_778_ = v_a_772_;
v_isShared_779_ = v_isSharedCheck_796_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_tail_776_);
lean_inc(v_head_775_);
lean_dec(v_a_772_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_796_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_795_; 
v_fst_780_ = lean_ctor_get(v_head_775_, 0);
v_snd_781_ = lean_ctor_get(v_head_775_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_head_775_);
if (v_isSharedCheck_795_ == 0)
{
v___x_783_ = v_head_775_;
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_head_775_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_795_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
uint8_t v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_785_ = lean_unbox(v_snd_781_);
lean_dec(v_snd_781_);
v___x_786_ = lean_bool_not(v___x_785_);
v___x_787_ = lean_box(v___x_786_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 1, v___x_787_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___x_787_);
v___x_789_ = v_reuseFailAlloc_794_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_a_773_);
lean_ctor_set(v___x_778_, 0, v___x_789_);
v___x_791_ = v___x_778_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_773_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v_a_772_ = v_tail_776_;
v_a_773_ = v___x_791_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object* v_n_797_, lean_object* v_f_798_, lean_object* v_c_799_, lean_object* v_rupHints_800_){
_start:
{
lean_object* v___x_801_; lean_object* v_negC_802_; lean_object* v___x_803_; lean_object* v_fst_804_; lean_object* v_snd_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_863_; 
v___x_801_ = lean_box(0);
lean_inc(v_c_799_);
v_negC_802_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v_c_799_, v___x_801_);
v___x_803_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(v_n_797_, v_f_798_, v_negC_802_);
v_fst_804_ = lean_ctor_get(v___x_803_, 0);
v_snd_805_ = lean_ctor_get(v___x_803_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_863_ == 0)
{
v___x_807_ = v___x_803_;
v_isShared_808_ = v_isSharedCheck_863_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snd_805_);
lean_inc(v_fst_804_);
lean_dec(v___x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_863_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v___x_809_; uint8_t v___x_810_; 
v___x_809_ = 1;
v___x_810_ = lean_unbox(v_snd_805_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v_snd_812_; lean_object* v_snd_813_; lean_object* v_snd_814_; uint8_t v___x_815_; 
lean_del_object(v___x_807_);
v___x_811_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_797_, v_fst_804_, v_rupHints_800_);
v_snd_812_ = lean_ctor_get(v___x_811_, 1);
lean_inc(v_snd_812_);
v_snd_813_ = lean_ctor_get(v_snd_812_, 1);
lean_inc(v_snd_813_);
v_snd_814_ = lean_ctor_get(v_snd_813_, 1);
v___x_815_ = lean_unbox(v_snd_814_);
if (v___x_815_ == 0)
{
lean_object* v_fst_816_; lean_object* v_fst_817_; lean_object* v_fst_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_845_; 
lean_inc(v_snd_814_);
lean_dec(v_snd_805_);
v_fst_816_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_fst_816_);
lean_dec_ref(v___x_811_);
v_fst_817_ = lean_ctor_get(v_snd_812_, 0);
lean_inc(v_fst_817_);
lean_dec(v_snd_812_);
v_fst_818_ = lean_ctor_get(v_snd_813_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_snd_813_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_snd_813_, 1);
lean_dec(v_unused_846_);
v___x_820_ = v_snd_813_;
v_isShared_821_ = v_isSharedCheck_845_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_fst_818_);
lean_dec(v_snd_813_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_845_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_unbox(v_fst_818_);
lean_dec(v_fst_818_);
v___x_823_ = lean_bool_not(v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v_clauses_824_; lean_object* v_rupUnits_825_; lean_object* v_ratUnits_826_; lean_object* v_assignments_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_841_; 
lean_dec(v_snd_814_);
v_clauses_824_ = lean_ctor_get(v_fst_816_, 0);
v_rupUnits_825_ = lean_ctor_get(v_fst_816_, 1);
v_ratUnits_826_ = lean_ctor_get(v_fst_816_, 2);
v_assignments_827_ = lean_ctor_get(v_fst_816_, 3);
v_isSharedCheck_841_ = !lean_is_exclusive(v_fst_816_);
if (v_isSharedCheck_841_ == 0)
{
v___x_829_ = v_fst_816_;
v_isShared_830_ = v_isSharedCheck_841_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_assignments_827_);
lean_inc(v_ratUnits_826_);
lean_inc(v_rupUnits_825_);
lean_inc(v_clauses_824_);
lean_dec(v_fst_816_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_841_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_assignments_831_; lean_object* v___x_833_; 
v_assignments_831_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_827_, v_fst_817_);
lean_dec(v_fst_817_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 3, v_assignments_831_);
v___x_833_ = v___x_829_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_clauses_824_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_rupUnits_825_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_ratUnits_826_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_assignments_831_);
v___x_833_ = v_reuseFailAlloc_840_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v_f_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v_f_834_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_797_, v___x_833_);
v___x_835_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_834_, v_c_799_);
v___x_836_ = lean_box(v___x_809_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_836_);
lean_ctor_set(v___x_820_, 0, v___x_835_);
v___x_838_ = v___x_820_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v___x_843_; 
lean_dec(v_fst_817_);
lean_dec(v_c_799_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v_fst_816_);
v___x_843_ = v___x_820_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_fst_816_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_snd_814_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_snd_812_);
lean_dec(v_c_799_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_snd_813_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; lean_object* v_unused_856_; 
v_unused_855_ = lean_ctor_get(v_snd_813_, 1);
lean_dec(v_unused_855_);
v_unused_856_ = lean_ctor_get(v_snd_813_, 0);
lean_dec(v_unused_856_);
v___x_848_ = v_snd_813_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_dec(v_snd_813_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_fst_850_; lean_object* v___x_852_; 
v_fst_850_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_fst_850_);
lean_dec_ref(v___x_811_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_snd_805_);
lean_ctor_set(v___x_848_, 0, v_fst_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_fst_850_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_snd_805_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_object* v_f_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_snd_805_);
v_f_857_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_797_, v_fst_804_);
v___x_858_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_857_, v_c_799_);
v___x_859_ = lean_box(v___x_809_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_859_);
lean_ctor_set(v___x_807_, 0, v___x_858_);
v___x_861_ = v___x_807_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(lean_object* v_n_864_, lean_object* v_f_865_, lean_object* v_c_866_, lean_object* v_rupHints_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_864_, v_f_865_, v_c_866_, v_rupHints_867_);
lean_dec_ref(v_rupHints_867_);
lean_dec(v_n_864_);
return v_res_868_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(lean_object* v_a_869_, lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
uint8_t v___x_871_; 
v___x_871_ = 0;
return v___x_871_;
}
else
{
lean_object* v_head_872_; lean_object* v_tail_873_; uint8_t v___y_875_; lean_object* v_fst_877_; lean_object* v_snd_878_; lean_object* v_fst_879_; lean_object* v_snd_880_; uint8_t v___x_881_; 
v_head_872_ = lean_ctor_get(v_x_870_, 0);
v_tail_873_ = lean_ctor_get(v_x_870_, 1);
v_fst_877_ = lean_ctor_get(v_a_869_, 0);
v_snd_878_ = lean_ctor_get(v_a_869_, 1);
v_fst_879_ = lean_ctor_get(v_head_872_, 0);
v_snd_880_ = lean_ctor_get(v_head_872_, 1);
v___x_881_ = lean_nat_dec_eq(v_fst_877_, v_fst_879_);
if (v___x_881_ == 0)
{
v___y_875_ = v___x_881_;
goto v___jp_874_;
}
else
{
uint8_t v___x_882_; 
v___x_882_ = lean_unbox(v_snd_878_);
if (v___x_882_ == 0)
{
uint8_t v___x_883_; 
v___x_883_ = lean_unbox(v_snd_880_);
if (v___x_883_ == 0)
{
v___y_875_ = v___x_881_;
goto v___jp_874_;
}
else
{
v_x_870_ = v_tail_873_;
goto _start;
}
}
else
{
uint8_t v___x_885_; 
v___x_885_ = lean_unbox(v_snd_880_);
v___y_875_ = v___x_885_;
goto v___jp_874_;
}
}
v___jp_874_:
{
if (v___y_875_ == 0)
{
v_x_870_ = v_tail_873_;
goto _start;
}
else
{
return v___y_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg___boxed(lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
uint8_t v_res_888_; lean_object* v_r_889_; 
v_res_888_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_a_886_, v_x_887_);
lean_dec(v_x_887_);
lean_dec_ref(v_a_886_);
v_r_889_ = lean_box(v_res_888_);
return v_r_889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(lean_object* v_clauses_890_, lean_object* v_n_891_, lean_object* v_negL_892_, lean_object* v_as_893_, size_t v_i_894_, size_t v_stop_895_, lean_object* v_b_896_){
_start:
{
lean_object* v___y_898_; uint8_t v___x_902_; 
v___x_902_ = lean_usize_dec_eq(v_i_894_, v_stop_895_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_903_ = lean_box(0);
v___x_904_ = lean_array_uget_borrowed(v_as_893_, v_i_894_);
v___x_905_ = lean_array_get_borrowed(v___x_903_, v_clauses_890_, v___x_904_);
if (lean_obj_tag(v___x_905_) == 0)
{
v___y_898_ = v_b_896_;
goto v___jp_897_;
}
else
{
lean_object* v_val_906_; uint8_t v___x_907_; 
v_val_906_ = lean_ctor_get(v___x_905_, 0);
v___x_907_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_negL_892_, v_val_906_);
if (v___x_907_ == 0)
{
v___y_898_ = v_b_896_;
goto v___jp_897_;
}
else
{
lean_object* v___x_908_; 
lean_inc(v___x_904_);
v___x_908_ = lean_array_push(v_b_896_, v___x_904_);
v___y_898_ = v___x_908_;
goto v___jp_897_;
}
}
}
else
{
return v_b_896_;
}
v___jp_897_:
{
size_t v___x_899_; size_t v___x_900_; 
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_894_, v___x_899_);
v_i_894_ = v___x_900_;
v_b_896_ = v___y_898_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1___boxed(lean_object* v_clauses_909_, lean_object* v_n_910_, lean_object* v_negL_911_, lean_object* v_as_912_, lean_object* v_i_913_, lean_object* v_stop_914_, lean_object* v_b_915_){
_start:
{
size_t v_i_boxed_916_; size_t v_stop_boxed_917_; lean_object* v_res_918_; 
v_i_boxed_916_ = lean_unbox_usize(v_i_913_);
lean_dec(v_i_913_);
v_stop_boxed_917_ = lean_unbox_usize(v_stop_914_);
lean_dec(v_stop_914_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_909_, v_n_910_, v_negL_911_, v_as_912_, v_i_boxed_916_, v_stop_boxed_917_, v_b_915_);
lean_dec_ref(v_as_912_);
lean_dec_ref(v_negL_911_);
lean_dec(v_n_910_);
lean_dec_ref(v_clauses_909_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(lean_object* v_n_921_, lean_object* v_clauses_922_, lean_object* v_l_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_924_ = lean_array_get_size(v_clauses_922_);
v___x_925_ = l_Array_range(v___x_924_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_array_get_size(v___x_925_);
v___x_928_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0));
v___x_929_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
if (v___x_929_ == 0)
{
lean_dec_ref(v___x_925_);
lean_dec_ref(v_l_923_);
return v___x_928_;
}
else
{
lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_948_; 
v_fst_930_ = lean_ctor_get(v_l_923_, 0);
v_snd_931_ = lean_ctor_get(v_l_923_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_l_923_);
if (v_isSharedCheck_948_ == 0)
{
v___x_933_ = v_l_923_;
v_isShared_934_ = v_isSharedCheck_948_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_930_);
lean_dec(v_l_923_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_948_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v_negL_939_; 
v___x_935_ = lean_unbox(v_snd_931_);
lean_dec(v_snd_931_);
v___x_936_ = lean_bool_not(v___x_935_);
v___x_937_ = lean_box(v___x_936_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_937_);
v_negL_939_ = v___x_933_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_fst_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_937_);
v_negL_939_ = v_reuseFailAlloc_947_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
uint8_t v___x_940_; 
v___x_940_ = lean_nat_dec_le(v___x_927_, v___x_927_);
if (v___x_940_ == 0)
{
if (v___x_929_ == 0)
{
lean_dec_ref(v_negL_939_);
lean_dec_ref(v___x_925_);
return v___x_928_;
}
else
{
size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
v___x_941_ = ((size_t)0ULL);
v___x_942_ = lean_usize_of_nat(v___x_927_);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_922_, v_n_921_, v_negL_939_, v___x_925_, v___x_941_, v___x_942_, v___x_928_);
lean_dec_ref(v___x_925_);
lean_dec_ref(v_negL_939_);
return v___x_943_;
}
}
else
{
size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_of_nat(v___x_927_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_922_, v_n_921_, v_negL_939_, v___x_925_, v___x_944_, v___x_945_, v___x_928_);
lean_dec_ref(v___x_925_);
lean_dec_ref(v_negL_939_);
return v___x_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___boxed(lean_object* v_n_949_, lean_object* v_clauses_950_, lean_object* v_l_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(v_n_949_, v_clauses_950_, v_l_951_);
lean_dec_ref(v_clauses_950_);
lean_dec(v_n_949_);
return v_res_952_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(lean_object* v_n_953_, lean_object* v_a_954_, lean_object* v_x_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_a_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___boxed(lean_object* v_n_957_, lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(v_n_957_, v_a_958_, v_x_959_);
lean_dec(v_x_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_n_957_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(size_t v_sz_962_, size_t v_i_963_, lean_object* v_bs_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = lean_usize_dec_lt(v_i_963_, v_sz_962_);
if (v___x_965_ == 0)
{
return v_bs_964_;
}
else
{
lean_object* v_v_966_; lean_object* v_fst_967_; lean_object* v___x_968_; lean_object* v_bs_x27_969_; size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; 
v_v_966_ = lean_array_uget_borrowed(v_bs_964_, v_i_963_);
v_fst_967_ = lean_ctor_get(v_v_966_, 0);
lean_inc(v_fst_967_);
v___x_968_ = lean_unsigned_to_nat(0u);
v_bs_x27_969_ = lean_array_uset(v_bs_964_, v_i_963_, v___x_968_);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_963_, v___x_970_);
v___x_972_ = lean_array_uset(v_bs_x27_969_, v_i_963_, v_fst_967_);
v_i_963_ = v___x_971_;
v_bs_964_ = v___x_972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0___boxed(lean_object* v_sz_974_, lean_object* v_i_975_, lean_object* v_bs_976_){
_start:
{
size_t v_sz_boxed_977_; size_t v_i_boxed_978_; lean_object* v_res_979_; 
v_sz_boxed_977_ = lean_unbox_usize(v_sz_974_);
lean_dec(v_sz_974_);
v_i_boxed_978_ = lean_unbox_usize(v_i_975_);
lean_dec(v_i_975_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(v_sz_boxed_977_, v_i_boxed_978_, v_bs_976_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(lean_object* v_xs_980_, lean_object* v_ys_981_, lean_object* v_x_982_){
_start:
{
lean_object* v_zero_983_; uint8_t v_isZero_984_; 
v_zero_983_ = lean_unsigned_to_nat(0u);
v_isZero_984_ = lean_nat_dec_eq(v_x_982_, v_zero_983_);
if (v_isZero_984_ == 1)
{
lean_dec(v_x_982_);
return v_isZero_984_;
}
else
{
lean_object* v_one_985_; lean_object* v_n_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_one_985_ = lean_unsigned_to_nat(1u);
v_n_986_ = lean_nat_sub(v_x_982_, v_one_985_);
lean_dec(v_x_982_);
v___x_987_ = lean_array_fget_borrowed(v_xs_980_, v_n_986_);
v___x_988_ = lean_array_fget_borrowed(v_ys_981_, v_n_986_);
v___x_989_ = lean_nat_dec_eq(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_dec(v_n_986_);
return v___x_989_;
}
else
{
v_x_982_ = v_n_986_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg___boxed(lean_object* v_xs_991_, lean_object* v_ys_992_, lean_object* v_x_993_){
_start:
{
uint8_t v_res_994_; lean_object* v_r_995_; 
v_res_994_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_991_, v_ys_992_, v_x_993_);
lean_dec_ref(v_ys_992_);
lean_dec_ref(v_xs_991_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT uint8_t l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(lean_object* v_xs_996_, lean_object* v_ys_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = lean_array_get_size(v_xs_996_);
v___x_999_ = lean_array_get_size(v_ys_997_);
v___x_1000_ = lean_nat_dec_eq(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
return v___x_1000_;
}
else
{
uint8_t v___x_1001_; 
v___x_1001_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_996_, v_ys_997_, v___x_998_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1___boxed(lean_object* v_xs_1002_, lean_object* v_ys_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(v_xs_1002_, v_ys_1003_);
lean_dec_ref(v_ys_1003_);
lean_dec_ref(v_xs_1002_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(lean_object* v_n_1006_, lean_object* v_f_1007_, lean_object* v_pivot_1008_, lean_object* v_ratHints_1009_){
_start:
{
lean_object* v_clauses_1010_; lean_object* v_ratClauseIndices_1011_; size_t v_sz_1012_; size_t v___x_1013_; lean_object* v_ratHintIndices_1014_; uint8_t v___x_1015_; 
v_clauses_1010_ = lean_ctor_get(v_f_1007_, 0);
v_ratClauseIndices_1011_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(v_n_1006_, v_clauses_1010_, v_pivot_1008_);
v_sz_1012_ = lean_array_size(v_ratHints_1009_);
v___x_1013_ = ((size_t)0ULL);
v_ratHintIndices_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(v_sz_1012_, v___x_1013_, v_ratHints_1009_);
v___x_1015_ = l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(v_ratClauseIndices_1011_, v_ratHintIndices_1014_);
lean_dec_ref(v_ratHintIndices_1014_);
lean_dec_ref(v_ratClauseIndices_1011_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive___boxed(lean_object* v_n_1016_, lean_object* v_f_1017_, lean_object* v_pivot_1018_, lean_object* v_ratHints_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(v_n_1016_, v_f_1017_, v_pivot_1018_, v_ratHints_1019_);
lean_dec_ref(v_f_1017_);
lean_dec(v_n_1016_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(lean_object* v_xs_1022_, lean_object* v_ys_1023_, lean_object* v_hsz_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_1022_, v_ys_1023_, v_x_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___boxed(lean_object* v_xs_1028_, lean_object* v_ys_1029_, lean_object* v_hsz_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(v_xs_1028_, v_ys_1029_, v_hsz_1030_, v_x_1031_, v_x_1032_);
lean_dec_ref(v_ys_1029_);
lean_dec_ref(v_xs_1028_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(lean_object* v_as_1035_, size_t v_i_1036_, size_t v_stop_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1036_, v_stop_1037_);
if (v___x_1039_ == 0)
{
size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_sub(v_i_1036_, v___x_1040_);
v___x_1042_ = lean_array_uget_borrowed(v_as_1035_, v___x_1041_);
lean_inc(v___x_1042_);
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_b_1038_);
v_i_1036_ = v___x_1041_;
v_b_1038_ = v___x_1043_;
goto _start;
}
else
{
return v_b_1038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0___boxed(lean_object* v_as_1045_, lean_object* v_i_1046_, lean_object* v_stop_1047_, lean_object* v_b_1048_){
_start:
{
size_t v_i_boxed_1049_; size_t v_stop_boxed_1050_; lean_object* v_res_1051_; 
v_i_boxed_1049_ = lean_unbox_usize(v_i_1046_);
lean_dec(v_i_1046_);
v_stop_boxed_1050_ = lean_unbox_usize(v_stop_1047_);
lean_dec(v_stop_1047_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(v_as_1045_, v_i_boxed_1049_, v_stop_boxed_1050_, v_b_1048_);
lean_dec_ref(v_as_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(lean_object* v_l_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
if (lean_obj_tag(v_a_1054_) == 0)
{
lean_dec_ref(v_a_1055_);
lean_inc(v_l_1052_);
return v_l_1052_;
}
else
{
lean_object* v_head_1056_; lean_object* v_tail_1057_; uint8_t v___y_1062_; lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v_fst_1071_; lean_object* v_snd_1072_; uint8_t v___x_1073_; 
v_head_1056_ = lean_ctor_get(v_a_1054_, 0);
lean_inc(v_head_1056_);
v_tail_1057_ = lean_ctor_get(v_a_1054_, 1);
lean_inc(v_tail_1057_);
lean_dec_ref_known(v_a_1054_, 2);
v_fst_1069_ = lean_ctor_get(v_head_1056_, 0);
v_snd_1070_ = lean_ctor_get(v_head_1056_, 1);
v_fst_1071_ = lean_ctor_get(v_a_1053_, 0);
v_snd_1072_ = lean_ctor_get(v_a_1053_, 1);
v___x_1073_ = lean_nat_dec_eq(v_fst_1069_, v_fst_1071_);
if (v___x_1073_ == 0)
{
v___y_1062_ = v___x_1073_;
goto v___jp_1061_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_unbox(v_snd_1070_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_unbox(v_snd_1072_);
if (v___x_1075_ == 0)
{
v___y_1062_ = v___x_1073_;
goto v___jp_1061_;
}
else
{
goto v___jp_1058_;
}
}
else
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_unbox(v_snd_1072_);
v___y_1062_ = v___x_1076_;
goto v___jp_1061_;
}
}
v___jp_1058_:
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_array_push(v_a_1055_, v_head_1056_);
v_a_1054_ = v_tail_1057_;
v_a_1055_ = v___x_1059_;
goto _start;
}
v___jp_1061_:
{
if (v___y_1062_ == 0)
{
goto v___jp_1058_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
lean_dec(v_head_1056_);
v___x_1063_ = lean_array_get_size(v_a_1055_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_nat_dec_lt(v___x_1064_, v___x_1063_);
if (v___x_1065_ == 0)
{
lean_dec_ref(v_a_1055_);
return v_tail_1057_;
}
else
{
size_t v___x_1066_; size_t v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_usize_of_nat(v___x_1063_);
v___x_1067_ = ((size_t)0ULL);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(v_a_1055_, v___x_1066_, v___x_1067_, v_tail_1057_);
lean_dec_ref(v_a_1055_);
return v___x_1068_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg___boxed(lean_object* v_l_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_l_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec_ref(v_a_1078_);
lean_dec(v_l_1077_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(lean_object* v_n_1082_, lean_object* v_f_1083_, lean_object* v_negPivot_1084_, lean_object* v_ratHint_1085_){
_start:
{
lean_object* v_clauses_1086_; lean_object* v_rupUnits_1087_; lean_object* v_ratUnits_1088_; lean_object* v_assignments_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1168_; 
v_clauses_1086_ = lean_ctor_get(v_f_1083_, 0);
v_rupUnits_1087_ = lean_ctor_get(v_f_1083_, 1);
v_ratUnits_1088_ = lean_ctor_get(v_f_1083_, 2);
v_assignments_1089_ = lean_ctor_get(v_f_1083_, 3);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_f_1083_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1091_ = v_f_1083_;
v_isShared_1092_ = v_isSharedCheck_1168_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_assignments_1089_);
lean_inc(v_ratUnits_1088_);
lean_inc(v_rupUnits_1087_);
lean_inc(v_clauses_1086_);
lean_dec(v_f_1083_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1168_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1167_; 
v_fst_1093_ = lean_ctor_get(v_ratHint_1085_, 0);
v_snd_1094_ = lean_ctor_get(v_ratHint_1085_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_ratHint_1085_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1096_ = v_ratHint_1085_;
v_isShared_1097_ = v_isSharedCheck_1167_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_snd_1094_);
lean_inc(v_fst_1093_);
lean_dec(v_ratHint_1085_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1167_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_array_get_borrowed(v___x_1098_, v_clauses_1086_, v_fst_1093_);
lean_dec(v_fst_1093_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1101_; 
lean_dec(v_snd_1094_);
if (v_isShared_1092_ == 0)
{
v___x_1101_ = v___x_1091_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_clauses_1086_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_rupUnits_1087_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_ratUnits_1088_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_assignments_1089_);
v___x_1101_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = 0;
v___x_1103_ = lean_box(v___x_1102_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 1, v___x_1103_);
lean_ctor_set(v___x_1096_, 0, v___x_1101_);
v___x_1105_ = v___x_1096_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_negC_1112_; lean_object* v___x_1114_; 
lean_del_object(v___x_1096_);
v_val_1108_ = lean_ctor_get(v___x_1099_, 0);
v___x_1109_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0));
lean_inc(v_val_1108_);
v___x_1110_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_val_1108_, v_negPivot_1084_, v_val_1108_, v___x_1109_);
v___x_1111_ = lean_box(0);
v_negC_1112_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v___x_1110_, v___x_1111_);
if (v_isShared_1092_ == 0)
{
v___x_1114_ = v___x_1091_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_clauses_1086_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_rupUnits_1087_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_ratUnits_1088_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_assignments_1089_);
v___x_1114_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1165_; 
v___x_1115_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(v___x_1114_, v_negC_1112_);
v_fst_1116_ = lean_ctor_get(v___x_1115_, 0);
v_snd_1117_ = lean_ctor_get(v___x_1115_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1119_ = v___x_1115_;
v_isShared_1120_ = v_isSharedCheck_1165_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_snd_1117_);
lean_inc(v_fst_1116_);
lean_dec(v___x_1115_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1165_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
uint8_t v___x_1121_; uint8_t v___x_1122_; 
v___x_1121_ = 1;
v___x_1122_ = lean_unbox(v_snd_1117_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v_snd_1124_; lean_object* v_snd_1125_; lean_object* v_fst_1126_; lean_object* v_fst_1127_; lean_object* v_fst_1128_; lean_object* v_snd_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1119_);
v___x_1123_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_1082_, v_fst_1116_, v_snd_1094_);
lean_dec(v_snd_1094_);
v_snd_1124_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_snd_1124_);
v_snd_1125_ = lean_ctor_get(v_snd_1124_, 1);
lean_inc(v_snd_1125_);
v_fst_1126_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_fst_1126_);
lean_dec_ref(v___x_1123_);
v_fst_1127_ = lean_ctor_get(v_snd_1124_, 0);
lean_inc(v_fst_1127_);
lean_dec(v_snd_1124_);
v_fst_1128_ = lean_ctor_get(v_snd_1125_, 0);
v_snd_1129_ = lean_ctor_get(v_snd_1125_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_snd_1125_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1131_ = v_snd_1125_;
v_isShared_1132_ = v_isSharedCheck_1159_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_snd_1129_);
lean_inc(v_fst_1128_);
lean_dec(v_snd_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1159_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_clauses_1133_; lean_object* v_rupUnits_1134_; lean_object* v_ratUnits_1135_; lean_object* v_assignments_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1158_; 
v_clauses_1133_ = lean_ctor_get(v_fst_1126_, 0);
v_rupUnits_1134_ = lean_ctor_get(v_fst_1126_, 1);
v_ratUnits_1135_ = lean_ctor_get(v_fst_1126_, 2);
v_assignments_1136_ = lean_ctor_get(v_fst_1126_, 3);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_fst_1126_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1138_ = v_fst_1126_;
v_isShared_1139_ = v_isSharedCheck_1158_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_assignments_1136_);
lean_inc(v_ratUnits_1135_);
lean_inc(v_rupUnits_1134_);
lean_inc(v_clauses_1133_);
lean_dec(v_fst_1126_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1158_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_assignments_1140_; lean_object* v___x_1142_; 
v_assignments_1140_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_1136_, v_fst_1127_);
lean_dec(v_fst_1127_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 3, v_assignments_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_clauses_1133_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_rupUnits_1134_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_ratUnits_1135_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_assignments_1140_);
v___x_1142_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v_f_1143_; uint8_t v___x_1144_; 
v_f_1143_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v___x_1142_);
v___x_1144_ = lean_unbox(v_snd_1129_);
lean_dec(v_snd_1129_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_unbox(v_fst_1128_);
lean_dec(v_fst_1128_);
v___x_1146_ = lean_bool_not(v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
lean_dec(v_snd_1117_);
v___x_1147_ = lean_box(v___x_1121_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v___x_1147_);
lean_ctor_set(v___x_1131_, 0, v_f_1143_);
v___x_1149_ = v___x_1131_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_f_1143_);
lean_ctor_set(v_reuseFailAlloc_1150_, 1, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v___x_1152_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_snd_1117_);
lean_ctor_set(v___x_1131_, 0, v_f_1143_);
v___x_1152_ = v___x_1131_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_f_1143_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_snd_1117_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec(v_fst_1128_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_snd_1117_);
lean_ctor_set(v___x_1131_, 0, v_f_1143_);
v___x_1155_ = v___x_1131_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_f_1143_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_snd_1117_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
else
{
lean_object* v_f_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_dec(v_snd_1117_);
lean_dec(v_snd_1094_);
v_f_1160_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v_fst_1116_);
v___x_1161_ = lean_box(v___x_1121_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v___x_1161_);
lean_ctor_set(v___x_1119_, 0, v_f_1160_);
v___x_1163_ = v___x_1119_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_f_1160_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___boxed(lean_object* v_n_1169_, lean_object* v_f_1170_, lean_object* v_negPivot_1171_, lean_object* v_ratHint_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(v_n_1169_, v_f_1170_, v_negPivot_1171_, v_ratHint_1172_);
lean_dec_ref(v_negPivot_1171_);
lean_dec(v_n_1169_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(lean_object* v_n_1174_, lean_object* v_l_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_l_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___boxed(lean_object* v_n_1180_, lean_object* v_l_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(v_n_1180_, v_l_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec_ref(v_a_1182_);
lean_dec(v_l_1181_);
lean_dec(v_n_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(lean_object* v_pivot_1186_, lean_object* v_n_1187_, lean_object* v_as_1188_, size_t v_i_1189_, size_t v_stop_1190_, lean_object* v_b_1191_){
_start:
{
lean_object* v___y_1193_; uint8_t v___x_1197_; 
v___x_1197_ = lean_usize_dec_eq(v_i_1189_, v_stop_1190_);
if (v___x_1197_ == 0)
{
lean_object* v_snd_1198_; uint8_t v___x_1199_; 
v_snd_1198_ = lean_ctor_get(v_b_1191_, 1);
v___x_1199_ = lean_unbox(v_snd_1198_);
if (v___x_1199_ == 0)
{
v___y_1193_ = v_b_1191_;
goto v___jp_1192_;
}
else
{
lean_object* v_fst_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1214_; 
v_fst_1200_ = lean_ctor_get(v_b_1191_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_b_1191_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; 
v_unused_1215_ = lean_ctor_get(v_b_1191_, 1);
lean_dec(v_unused_1215_);
v___x_1202_ = v_b_1191_;
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_fst_1200_);
lean_dec(v_b_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1214_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_fst_1204_; lean_object* v_snd_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v_fst_1204_ = lean_ctor_get(v_pivot_1186_, 0);
v_snd_1205_ = lean_ctor_get(v_pivot_1186_, 1);
v___x_1206_ = lean_array_uget_borrowed(v_as_1188_, v_i_1189_);
v___x_1207_ = lean_unbox(v_snd_1205_);
v___x_1208_ = lean_bool_not(v___x_1207_);
v___x_1209_ = lean_box(v___x_1208_);
lean_inc(v_fst_1204_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1209_);
lean_ctor_set(v___x_1202_, 0, v_fst_1204_);
v___x_1211_ = v___x_1202_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_fst_1204_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; 
lean_inc(v___x_1206_);
v___x_1212_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(v_n_1187_, v_fst_1200_, v___x_1211_, v___x_1206_);
lean_dec_ref(v___x_1211_);
v___y_1193_ = v___x_1212_;
goto v___jp_1192_;
}
}
}
}
else
{
return v_b_1191_;
}
v___jp_1192_:
{
size_t v___x_1194_; size_t v___x_1195_; 
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1189_, v___x_1194_);
v_i_1189_ = v___x_1195_;
v_b_1191_ = v___y_1193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(lean_object* v_pivot_1216_, lean_object* v_n_1217_, lean_object* v_as_1218_, lean_object* v_i_1219_, lean_object* v_stop_1220_, lean_object* v_b_1221_){
_start:
{
size_t v_i_boxed_1222_; size_t v_stop_boxed_1223_; lean_object* v_res_1224_; 
v_i_boxed_1222_ = lean_unbox_usize(v_i_1219_);
lean_dec(v_i_1219_);
v_stop_boxed_1223_ = lean_unbox_usize(v_stop_1220_);
lean_dec(v_stop_1220_);
v_res_1224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v_pivot_1216_, v_n_1217_, v_as_1218_, v_i_boxed_1222_, v_stop_boxed_1223_, v_b_1221_);
lean_dec_ref(v_as_1218_);
lean_dec(v_n_1217_);
lean_dec_ref(v_pivot_1216_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object* v_n_1225_, lean_object* v_f_1226_, lean_object* v_c_1227_, lean_object* v_pivot_1228_, lean_object* v_rupHints_1229_, lean_object* v_ratHints_1230_){
_start:
{
uint8_t v___x_1231_; 
lean_inc_ref(v_ratHints_1230_);
lean_inc_ref(v_pivot_1228_);
v___x_1231_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(v_n_1225_, v_f_1226_, v_pivot_1228_, v_ratHints_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
lean_dec(v_c_1227_);
v___x_1232_ = lean_box(v___x_1231_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_f_1226_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v_negC_1235_; lean_object* v___x_1236_; lean_object* v_snd_1237_; uint8_t v___x_1238_; 
v___x_1234_ = lean_box(0);
lean_inc(v_c_1227_);
v_negC_1235_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v_c_1227_, v___x_1234_);
v___x_1236_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(v_n_1225_, v_f_1226_, v_negC_1235_);
v_snd_1237_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_snd_1237_);
v___x_1238_ = lean_unbox(v_snd_1237_);
if (v___x_1238_ == 0)
{
lean_object* v_fst_1239_; lean_object* v___x_1240_; lean_object* v_snd_1241_; lean_object* v_snd_1242_; lean_object* v_fst_1243_; lean_object* v_fst_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1306_; 
v_fst_1239_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_fst_1239_);
lean_dec_ref(v___x_1236_);
v___x_1240_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(v_n_1225_, v_fst_1239_, v_rupHints_1229_);
v_snd_1241_ = lean_ctor_get(v___x_1240_, 1);
lean_inc(v_snd_1241_);
v_snd_1242_ = lean_ctor_get(v_snd_1241_, 1);
lean_inc(v_snd_1242_);
v_fst_1243_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_fst_1243_);
lean_dec_ref(v___x_1240_);
v_fst_1244_ = lean_ctor_get(v_snd_1241_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_snd_1241_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_snd_1241_, 1);
lean_dec(v_unused_1307_);
v___x_1246_ = v_snd_1241_;
v_isShared_1247_ = v_isSharedCheck_1306_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_fst_1244_);
lean_dec(v_snd_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1306_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_fst_1248_; lean_object* v_snd_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1305_; 
v_fst_1248_ = lean_ctor_get(v_snd_1242_, 0);
v_snd_1249_ = lean_ctor_get(v_snd_1242_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_snd_1242_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1251_ = v_snd_1242_;
v_isShared_1252_ = v_isSharedCheck_1305_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1248_);
lean_dec(v_snd_1242_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1305_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_fst_1254_; uint8_t v_snd_1255_; lean_object* v___y_1279_; uint8_t v___x_1283_; 
v___x_1283_ = lean_unbox(v_snd_1249_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
lean_dec(v_snd_1237_);
v___x_1284_ = lean_unbox(v_fst_1248_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
lean_dec(v_snd_1249_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_array_get_size(v_ratHints_1230_);
v___x_1287_ = lean_nat_dec_lt(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_del_object(v___x_1246_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
v_fst_1254_ = v_fst_1243_;
v_snd_1255_ = v___x_1231_;
goto v___jp_1253_;
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(v___x_1231_);
lean_inc(v_fst_1243_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v___x_1288_);
lean_ctor_set(v___x_1246_, 0, v_fst_1243_);
v___x_1290_ = v___x_1246_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_fst_1243_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_nat_dec_le(v___x_1286_, v___x_1286_);
if (v___x_1291_ == 0)
{
if (v___x_1287_ == 0)
{
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
v_fst_1254_ = v_fst_1243_;
v_snd_1255_ = v___x_1231_;
goto v___jp_1253_;
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v_fst_1243_);
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1286_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v_pivot_1228_, v_n_1225_, v_ratHints_1230_, v___x_1292_, v___x_1293_, v___x_1290_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
v___y_1279_ = v___x_1294_;
goto v___jp_1278_;
}
}
else
{
size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v_fst_1243_);
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1286_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v_pivot_1228_, v_n_1225_, v_ratHints_1230_, v___x_1295_, v___x_1296_, v___x_1290_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
v___y_1279_ = v___x_1297_;
goto v___jp_1278_;
}
}
}
}
else
{
lean_object* v___x_1300_; 
lean_del_object(v___x_1251_);
lean_dec(v_fst_1248_);
lean_dec(v_fst_1244_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
lean_dec(v_c_1227_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_snd_1249_);
lean_ctor_set(v___x_1246_, 0, v_fst_1243_);
v___x_1300_ = v___x_1246_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_fst_1243_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_snd_1249_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v___x_1303_; 
lean_del_object(v___x_1251_);
lean_dec(v_snd_1249_);
lean_dec(v_fst_1248_);
lean_dec(v_fst_1244_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
lean_dec(v_c_1227_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_snd_1237_);
lean_ctor_set(v___x_1246_, 0, v_fst_1243_);
v___x_1303_ = v___x_1246_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_fst_1243_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_snd_1237_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
v___jp_1253_:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_bool_not(v_snd_1255_);
if (v___x_1256_ == 0)
{
lean_object* v_clauses_1257_; lean_object* v_rupUnits_1258_; lean_object* v_ratUnits_1259_; lean_object* v_assignments_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_fst_1248_);
v_clauses_1257_ = lean_ctor_get(v_fst_1254_, 0);
v_rupUnits_1258_ = lean_ctor_get(v_fst_1254_, 1);
v_ratUnits_1259_ = lean_ctor_get(v_fst_1254_, 2);
v_assignments_1260_ = lean_ctor_get(v_fst_1254_, 3);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_fst_1254_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1262_ = v_fst_1254_;
v_isShared_1263_ = v_isSharedCheck_1274_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_assignments_1260_);
lean_inc(v_ratUnits_1259_);
lean_inc(v_rupUnits_1258_);
lean_inc(v_clauses_1257_);
lean_dec(v_fst_1254_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1274_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_assignments_1264_; lean_object* v___x_1266_; 
v_assignments_1264_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_1260_, v_fst_1244_);
lean_dec(v_fst_1244_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 3, v_assignments_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_clauses_1257_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_rupUnits_1258_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_ratUnits_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_assignments_1264_);
v___x_1266_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v_f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v_f_1267_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_1225_, v___x_1266_);
v___x_1268_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_1267_, v_c_1227_);
v___x_1269_ = lean_box(v___x_1231_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1269_);
lean_ctor_set(v___x_1251_, 0, v___x_1268_);
v___x_1271_ = v___x_1251_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v___x_1276_; 
lean_dec(v_fst_1244_);
lean_dec(v_c_1227_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_fst_1248_);
lean_ctor_set(v___x_1251_, 0, v_fst_1254_);
v___x_1276_ = v___x_1251_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_fst_1254_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_fst_1248_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
v___jp_1278_:
{
lean_object* v_fst_1280_; lean_object* v_snd_1281_; uint8_t v___x_1282_; 
v_fst_1280_ = lean_ctor_get(v___y_1279_, 0);
lean_inc(v_fst_1280_);
v_snd_1281_ = lean_ctor_get(v___y_1279_, 1);
lean_inc(v_snd_1281_);
lean_dec_ref(v___y_1279_);
v___x_1282_ = lean_unbox(v_snd_1281_);
lean_dec(v_snd_1281_);
v_fst_1254_ = v_fst_1280_;
v_snd_1255_ = v___x_1282_;
goto v___jp_1253_;
}
}
}
}
else
{
lean_object* v_fst_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_snd_1237_);
lean_dec_ref(v_ratHints_1230_);
lean_dec_ref(v_pivot_1228_);
lean_dec(v_c_1227_);
v_fst_1308_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1236_, 1);
lean_dec(v_unused_1318_);
v___x_1310_ = v___x_1236_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_fst_1308_);
lean_dec(v___x_1236_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1312_ = 0;
v___x_1313_ = lean_box(v___x_1312_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v___x_1313_);
v___x_1315_ = v___x_1310_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_fst_1308_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(lean_object* v_n_1319_, lean_object* v_f_1320_, lean_object* v_c_1321_, lean_object* v_pivot_1322_, lean_object* v_rupHints_1323_, lean_object* v_ratHints_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_1319_, v_f_1320_, v_c_1321_, v_pivot_1322_, v_rupHints_1323_, v_ratHints_1324_);
lean_dec_ref(v_rupHints_1323_);
lean_dec(v_n_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(lean_object* v_x_1326_, lean_object* v_x_1327_){
_start:
{
if (lean_obj_tag(v_x_1326_) == 0)
{
if (lean_obj_tag(v_x_1327_) == 0)
{
uint8_t v___x_1328_; 
v___x_1328_ = 1;
return v___x_1328_;
}
else
{
uint8_t v___x_1329_; 
v___x_1329_ = 0;
return v___x_1329_;
}
}
else
{
if (lean_obj_tag(v_x_1327_) == 0)
{
uint8_t v___x_1330_; 
v___x_1330_ = 0;
return v___x_1330_;
}
else
{
lean_object* v_val_1331_; lean_object* v_val_1332_; uint8_t v___x_1333_; 
v_val_1331_ = lean_ctor_get(v_x_1326_, 0);
v_val_1332_ = lean_ctor_get(v_x_1327_, 0);
v___x_1333_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_val_1331_, v_val_1332_);
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg___boxed(lean_object* v_x_1334_, lean_object* v_x_1335_){
_start:
{
uint8_t v_res_1336_; lean_object* v_r_1337_; 
v_res_1336_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_x_1334_, v_x_1335_);
lean_dec(v_x_1335_);
lean_dec(v_x_1334_);
v_r_1337_ = lean_box(v_res_1336_);
return v_r_1337_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(lean_object* v_n_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
uint8_t v___x_1341_; 
v___x_1341_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_x_1339_, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___boxed(lean_object* v_n_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_res_1345_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(v_n_1342_, v_x_1343_, v_x_1344_);
lean_dec(v_x_1344_);
lean_dec(v_x_1343_);
lean_dec(v_n_1342_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(lean_object* v_n_1347_, lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_){
_start:
{
lean_object* v_a_1353_; uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1357_ == 0)
{
return v_b_1351_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; uint8_t v___x_1361_; 
v_a_1358_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
v___x_1359_ = lean_box(0);
v___x_1360_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_a_1358_, v___x_1359_);
v___x_1361_ = lean_bool_not(v___x_1360_);
if (v___x_1361_ == 0)
{
v_a_1353_ = v_b_1351_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_unsigned_to_nat(1u);
v___x_1363_ = lean_nat_add(v_b_1351_, v___x_1362_);
lean_dec(v_b_1351_);
v_a_1353_ = v___x_1363_;
goto v___jp_1352_;
}
}
v___jp_1352_:
{
size_t v___x_1354_; size_t v___x_1355_; 
v___x_1354_ = ((size_t)1ULL);
v___x_1355_ = lean_usize_add(v_i_1350_, v___x_1354_);
v_i_1350_ = v___x_1355_;
v_b_1351_ = v_a_1353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1___boxed(lean_object* v_n_1364_, lean_object* v_as_1365_, lean_object* v_sz_1366_, lean_object* v_i_1367_, lean_object* v_b_1368_){
_start:
{
size_t v_sz_boxed_1369_; size_t v_i_boxed_1370_; lean_object* v_res_1371_; 
v_sz_boxed_1369_ = lean_unbox_usize(v_sz_1366_);
lean_dec(v_sz_1366_);
v_i_boxed_1370_ = lean_unbox_usize(v_i_1367_);
lean_dec(v_i_1367_);
v_res_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(v_n_1364_, v_as_1365_, v_sz_boxed_1369_, v_i_boxed_1370_, v_b_1368_);
lean_dec_ref(v_as_1365_);
lean_dec(v_n_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(lean_object* v_n_1372_, lean_object* v_f_1373_){
_start:
{
lean_object* v_clauses_1374_; lean_object* v_numClauses_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v_clauses_1374_ = lean_ctor_get(v_f_1373_, 0);
v_numClauses_1375_ = lean_unsigned_to_nat(0u);
v_sz_1376_ = lean_array_size(v_clauses_1374_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(v_n_1372_, v_clauses_1374_, v_sz_1376_, v___x_1377_, v_numClauses_1375_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula___boxed(lean_object* v_n_1379_, lean_object* v_f_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(v_n_1379_, v_f_1380_);
lean_dec_ref(v_f_1380_);
lean_dec(v_n_1379_);
return v_res_1381_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
