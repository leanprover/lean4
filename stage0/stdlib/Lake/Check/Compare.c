// Lean compiler output
// Module: Lake.Check.Compare
// Imports: public import LeanExport.Parse import Lake.Check.Util import Init.Data.ToString.Macro import Std.Data.HashSet
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_instBEqAxiomVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqTheoremVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqConstantVal_beq(lean_object*, lean_object*);
lean_object* l_Lean_QuotKind_ctorIdx(uint8_t);
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqQuotKind__lake_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqQuotKind__lake_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_Compare_instBEqQuotKind__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_Compare_instBEqQuotKind__lake_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_Compare_instBEqQuotKind__lake___closed__0 = (const lean_object*)&l_Lake_Check_Compare_instBEqQuotKind__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_Compare_instBEqQuotKind__lake = (const lean_object*)&l_Lake_Check_Compare_instBEqQuotKind__lake___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqQuotVal__lake_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqQuotVal__lake_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_Compare_instBEqQuotVal__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_Compare_instBEqQuotVal__lake_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_Compare_instBEqQuotVal__lake___closed__0 = (const lean_object*)&l_Lake_Check_Compare_instBEqQuotVal__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_Compare_instBEqQuotVal__lake = (const lean_object*)&l_Lake_Check_Compare_instBEqQuotVal__lake___closed__0_value;
LEAN_EXPORT uint8_t l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqInductiveVal__lake_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqInductiveVal__lake_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_Compare_instBEqInductiveVal__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_Compare_instBEqInductiveVal__lake_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_Compare_instBEqInductiveVal__lake___closed__0 = (const lean_object*)&l_Lake_Check_Compare_instBEqInductiveVal__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_Compare_instBEqInductiveVal__lake = (const lean_object*)&l_Lake_Check_Compare_instBEqInductiveVal__lake___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqConstantInfo__lake_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqConstantInfo__lake_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_Compare_instBEqConstantInfo__lake___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_Compare_instBEqConstantInfo__lake_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Check_Compare_instBEqConstantInfo__lake___closed__0 = (const lean_object*)&l_Lake_Check_Compare_instBEqConstantInfo__lake___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Check_Compare_instBEqConstantInfo__lake = (const lean_object*)&l_Lake_Check_Compare_instBEqConstantInfo__lake___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___closed__0 = (const lean_object*)&l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___closed__0_value;
static const lean_ctor_object l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed__const__1 = (const lean_object*)&l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___closed__0 = (const lean_object*)&l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Const does not match between challenge and target '"};
static const lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0 = (const lean_object*)&l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0_value;
static const lean_string_object l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1 = (const lean_object*)&l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1_value;
static const lean_string_object l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Const not found in solution '"};
static const lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2 = (const lean_object*)&l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2_value;
static const lean_string_object l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Const not found in challenge '"};
static const lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3 = (const lean_object*)&l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Check_definitionHoleMatches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_definitionHoleMatches___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Solution constant is not a definition: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Challenge constant is not a definition: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Const not found in solution: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Const not found in challenge: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Challenge and solution constant kind don't match: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Challenge and solution theorem statement do not match: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Check_compareAt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_compareAt___closed__0;
static lean_once_cell_t l_Lake_Check_compareAt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_compareAt___closed__1;
LEAN_EXPORT lean_object* l_Lake_Check_compareAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_compareAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqQuotKind__lake_beq(uint8_t v_x_1_, uint8_t v_y_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = l_Lean_QuotKind_ctorIdx(v_x_1_);
v___x_4_ = l_Lean_QuotKind_ctorIdx(v_y_2_);
v___x_5_ = lean_nat_dec_eq(v___x_3_, v___x_4_);
lean_dec(v___x_4_);
lean_dec(v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqQuotKind__lake_beq___boxed(lean_object* v_x_6_, lean_object* v_y_7_){
_start:
{
uint8_t v_x_21__boxed_8_; uint8_t v_y_22__boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_x_21__boxed_8_ = lean_unbox(v_x_6_);
v_y_22__boxed_9_ = lean_unbox(v_y_7_);
v_res_10_ = l_Lake_Check_Compare_instBEqQuotKind__lake_beq(v_x_21__boxed_8_, v_y_22__boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqQuotVal__lake_beq(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_toConstantVal_16_; uint8_t v_kind_17_; lean_object* v_toConstantVal_18_; uint8_t v_kind_19_; uint8_t v___x_20_; 
v_toConstantVal_16_ = lean_ctor_get(v_x_14_, 0);
v_kind_17_ = lean_ctor_get_uint8(v_x_14_, sizeof(void*)*1);
v_toConstantVal_18_ = lean_ctor_get(v_x_15_, 0);
v_kind_19_ = lean_ctor_get_uint8(v_x_15_, sizeof(void*)*1);
v___x_20_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_16_, v_toConstantVal_18_);
if (v___x_20_ == 0)
{
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = l_Lake_Check_Compare_instBEqQuotKind__lake_beq(v_kind_17_, v_kind_19_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqQuotVal__lake_beq___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lake_Check_Compare_instBEqQuotVal__lake_beq(v_x_22_, v_x_23_);
lean_dec_ref(v_x_23_);
lean_dec_ref(v_x_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
if (lean_obj_tag(v_x_29_) == 0)
{
uint8_t v___x_30_; 
v___x_30_ = 1;
return v___x_30_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
else
{
if (lean_obj_tag(v_x_29_) == 0)
{
uint8_t v___x_32_; 
v___x_32_ = 0;
return v___x_32_;
}
else
{
lean_object* v_head_33_; lean_object* v_tail_34_; lean_object* v_head_35_; lean_object* v_tail_36_; uint8_t v___x_37_; 
v_head_33_ = lean_ctor_get(v_x_28_, 0);
v_tail_34_ = lean_ctor_get(v_x_28_, 1);
v_head_35_ = lean_ctor_get(v_x_29_, 0);
v_tail_36_ = lean_ctor_get(v_x_29_, 1);
v___x_37_ = lean_name_eq(v_head_33_, v_head_35_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
v_x_28_ = v_tail_34_;
v_x_29_ = v_tail_36_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0___boxed(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0(v_x_39_, v_x_40_);
lean_dec(v_x_40_);
lean_dec(v_x_39_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqInductiveVal__lake_beq(lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
lean_object* v_toConstantVal_45_; lean_object* v_numParams_46_; lean_object* v_numIndices_47_; lean_object* v_all_48_; lean_object* v_ctors_49_; lean_object* v_numNested_50_; uint8_t v_isRec_51_; uint8_t v_isUnsafe_52_; uint8_t v_isReflexive_53_; lean_object* v_toConstantVal_54_; lean_object* v_numParams_55_; lean_object* v_numIndices_56_; lean_object* v_all_57_; lean_object* v_ctors_58_; lean_object* v_numNested_59_; uint8_t v_isRec_60_; uint8_t v_isUnsafe_61_; uint8_t v_isReflexive_62_; uint8_t v___y_64_; uint8_t v___y_66_; uint8_t v___x_67_; 
v_toConstantVal_45_ = lean_ctor_get(v_x_43_, 0);
v_numParams_46_ = lean_ctor_get(v_x_43_, 1);
v_numIndices_47_ = lean_ctor_get(v_x_43_, 2);
v_all_48_ = lean_ctor_get(v_x_43_, 3);
v_ctors_49_ = lean_ctor_get(v_x_43_, 4);
v_numNested_50_ = lean_ctor_get(v_x_43_, 5);
v_isRec_51_ = lean_ctor_get_uint8(v_x_43_, sizeof(void*)*6);
v_isUnsafe_52_ = lean_ctor_get_uint8(v_x_43_, sizeof(void*)*6 + 1);
v_isReflexive_53_ = lean_ctor_get_uint8(v_x_43_, sizeof(void*)*6 + 2);
v_toConstantVal_54_ = lean_ctor_get(v_x_44_, 0);
v_numParams_55_ = lean_ctor_get(v_x_44_, 1);
v_numIndices_56_ = lean_ctor_get(v_x_44_, 2);
v_all_57_ = lean_ctor_get(v_x_44_, 3);
v_ctors_58_ = lean_ctor_get(v_x_44_, 4);
v_numNested_59_ = lean_ctor_get(v_x_44_, 5);
v_isRec_60_ = lean_ctor_get_uint8(v_x_44_, sizeof(void*)*6);
v_isUnsafe_61_ = lean_ctor_get_uint8(v_x_44_, sizeof(void*)*6 + 1);
v_isReflexive_62_ = lean_ctor_get_uint8(v_x_44_, sizeof(void*)*6 + 2);
v___x_67_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_45_, v_toConstantVal_54_);
if (v___x_67_ == 0)
{
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = lean_nat_dec_eq(v_numParams_46_, v_numParams_55_);
if (v___x_68_ == 0)
{
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = lean_nat_dec_eq(v_numIndices_47_, v_numIndices_56_);
if (v___x_69_ == 0)
{
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
v___x_70_ = l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0(v_all_48_, v_all_57_);
if (v___x_70_ == 0)
{
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = l_List_beq___at___00Lake_Check_Compare_instBEqInductiveVal__lake_beq_spec__0(v_ctors_49_, v_ctors_58_);
if (v___x_71_ == 0)
{
return v___x_71_;
}
else
{
uint8_t v___x_72_; 
v___x_72_ = lean_nat_dec_eq(v_numNested_50_, v_numNested_59_);
if (v___x_72_ == 0)
{
return v___x_72_;
}
else
{
if (v_isRec_60_ == 0)
{
if (v_isRec_51_ == 0)
{
v___y_66_ = v___x_72_;
goto v___jp_65_;
}
else
{
return v_isRec_60_;
}
}
else
{
v___y_66_ = v_isRec_51_;
goto v___jp_65_;
}
}
}
}
}
}
}
v___jp_63_:
{
if (v_isReflexive_62_ == 0)
{
if (v_isReflexive_53_ == 0)
{
return v___y_64_;
}
else
{
return v_isReflexive_62_;
}
}
else
{
return v_isReflexive_53_;
}
}
v___jp_65_:
{
if (v___y_66_ == 0)
{
return v___y_66_;
}
else
{
if (v_isUnsafe_61_ == 0)
{
if (v_isUnsafe_52_ == 0)
{
v___y_64_ = v___y_66_;
goto v___jp_63_;
}
else
{
return v_isUnsafe_61_;
}
}
else
{
if (v_isUnsafe_52_ == 0)
{
return v_isUnsafe_52_;
}
else
{
v___y_64_ = v_isUnsafe_52_;
goto v___jp_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqInductiveVal__lake_beq___boxed(lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lake_Check_Compare_instBEqInductiveVal__lake_beq(v_x_73_, v_x_74_);
lean_dec_ref(v_x_74_);
lean_dec_ref(v_x_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Lake_Check_Compare_instBEqConstantInfo__lake_beq(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
switch(lean_obj_tag(v_x_79_))
{
case 0:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_val_81_; lean_object* v_val_82_; uint8_t v___x_83_; 
v_val_81_ = lean_ctor_get(v_x_79_, 0);
v_val_82_ = lean_ctor_get(v_x_80_, 0);
v___x_83_ = l_Lean_instBEqAxiomVal_beq(v_val_81_, v_val_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
case 1:
{
if (lean_obj_tag(v_x_80_) == 1)
{
lean_object* v_val_85_; lean_object* v_val_86_; uint8_t v___x_87_; 
v_val_85_ = lean_ctor_get(v_x_79_, 0);
v_val_86_ = lean_ctor_get(v_x_80_, 0);
v___x_87_ = l_Lean_instBEqDefinitionVal_beq(v_val_85_, v_val_86_);
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
case 2:
{
if (lean_obj_tag(v_x_80_) == 2)
{
lean_object* v_val_89_; lean_object* v_val_90_; uint8_t v___x_91_; 
v_val_89_ = lean_ctor_get(v_x_79_, 0);
v_val_90_ = lean_ctor_get(v_x_80_, 0);
v___x_91_ = l_Lean_instBEqTheoremVal_beq(v_val_89_, v_val_90_);
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
case 3:
{
if (lean_obj_tag(v_x_80_) == 3)
{
lean_object* v_val_93_; lean_object* v_val_94_; uint8_t v___x_95_; 
v_val_93_ = lean_ctor_get(v_x_79_, 0);
v_val_94_ = lean_ctor_get(v_x_80_, 0);
v___x_95_ = l_Lean_instBEqOpaqueVal_beq(v_val_93_, v_val_94_);
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
case 4:
{
if (lean_obj_tag(v_x_80_) == 4)
{
lean_object* v_val_97_; lean_object* v_val_98_; uint8_t v___x_99_; 
v_val_97_ = lean_ctor_get(v_x_79_, 0);
v_val_98_ = lean_ctor_get(v_x_80_, 0);
v___x_99_ = l_Lake_Check_Compare_instBEqQuotVal__lake_beq(v_val_97_, v_val_98_);
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 0;
return v___x_100_;
}
}
case 5:
{
if (lean_obj_tag(v_x_80_) == 5)
{
lean_object* v_val_101_; lean_object* v_val_102_; uint8_t v___x_103_; 
v_val_101_ = lean_ctor_get(v_x_79_, 0);
v_val_102_ = lean_ctor_get(v_x_80_, 0);
v___x_103_ = l_Lake_Check_Compare_instBEqInductiveVal__lake_beq(v_val_101_, v_val_102_);
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
case 6:
{
if (lean_obj_tag(v_x_80_) == 6)
{
lean_object* v_val_105_; lean_object* v_val_106_; uint8_t v___x_107_; 
v_val_105_ = lean_ctor_get(v_x_79_, 0);
v_val_106_ = lean_ctor_get(v_x_80_, 0);
v___x_107_ = l_Lean_instBEqConstructorVal_beq(v_val_105_, v_val_106_);
return v___x_107_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
default: 
{
if (lean_obj_tag(v_x_80_) == 7)
{
lean_object* v_val_109_; lean_object* v_val_110_; uint8_t v___x_111_; 
v_val_109_ = lean_ctor_get(v_x_79_, 0);
v_val_110_ = lean_ctor_get(v_x_80_, 0);
v___x_111_ = l_Lean_instBEqRecursorVal_beq(v_val_109_, v_val_110_);
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_Compare_instBEqConstantInfo__lake_beq___boxed(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lake_Check_Compare_instBEqConstantInfo__lake_beq(v_x_113_, v_x_114_);
lean_dec_ref(v_x_114_);
lean_dec_ref(v_x_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(lean_object* v_a_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
else
{
lean_object* v_key_122_; lean_object* v_tail_123_; uint8_t v___x_124_; 
v_key_122_ = lean_ctor_get(v_x_120_, 0);
v_tail_123_ = lean_ctor_get(v_x_120_, 2);
v___x_124_ = lean_name_eq(v_key_122_, v_a_119_);
if (v___x_124_ == 0)
{
v_x_120_ = v_tail_123_;
goto _start;
}
else
{
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg___boxed(lean_object* v_a_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v_a_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(lean_object* v_m_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_buckets_132_; lean_object* v___x_133_; uint64_t v___y_135_; 
v_buckets_132_ = lean_ctor_get(v_m_130_, 1);
v___x_133_ = lean_array_get_size(v_buckets_132_);
if (lean_obj_tag(v_a_131_) == 0)
{
uint64_t v___x_149_; 
v___x_149_ = 1723ULL;
v___y_135_ = v___x_149_;
goto v___jp_134_;
}
else
{
uint64_t v_hash_150_; 
v_hash_150_ = lean_ctor_get_uint64(v_a_131_, sizeof(void*)*2);
v___y_135_ = v_hash_150_;
goto v___jp_134_;
}
v___jp_134_:
{
uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_136_ = 32ULL;
v___x_137_ = lean_uint64_shift_right(v___y_135_, v___x_136_);
v_fold_138_ = lean_uint64_xor(v___y_135_, v___x_137_);
v___x_139_ = 16ULL;
v___x_140_ = lean_uint64_shift_right(v_fold_138_, v___x_139_);
v___x_141_ = lean_uint64_xor(v_fold_138_, v___x_140_);
v___x_142_ = lean_uint64_to_usize(v___x_141_);
v___x_143_ = lean_usize_of_nat(v___x_133_);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v___x_143_, v___x_144_);
v___x_146_ = lean_usize_land(v___x_142_, v___x_145_);
v___x_147_ = lean_array_uget_borrowed(v_buckets_132_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_131_, v___x_147_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg___boxed(lean_object* v_m_151_, lean_object* v_a_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_m_151_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(lean_object* v_n_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_worklist_157_; lean_object* v_checked_158_; uint8_t v___x_159_; 
v_worklist_157_ = lean_ctor_get(v_a_156_, 0);
v_checked_158_ = lean_ctor_get(v_a_156_, 1);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_158_, v_n_155_);
if (v___x_159_ == 0)
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_170_; 
lean_inc_ref(v_checked_158_);
lean_inc_ref(v_worklist_157_);
v_isSharedCheck_170_ = !lean_is_exclusive(v_a_156_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; lean_object* v_unused_172_; 
v_unused_171_ = lean_ctor_get(v_a_156_, 1);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_a_156_, 0);
lean_dec(v_unused_172_);
v___x_161_ = v_a_156_;
v_isShared_162_ = v_isSharedCheck_170_;
goto v_resetjp_160_;
}
else
{
lean_dec(v_a_156_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_170_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_array_push(v_worklist_157_, v_n_155_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_checked_158_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_163_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_n_155_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_156_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(lean_object* v_n_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(v_n_176_, v_a_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___boxed(lean_object* v_n_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(v_n_180_, v_a_181_, v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_183_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_a_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_185_, v_a_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___boxed(lean_object* v_00_u03b2_188_, lean_object* v_m_189_, lean_object* v_a_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(v_00_u03b2_188_, v_m_189_, v_a_190_);
lean_dec(v_a_190_);
lean_dec_ref(v_m_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(lean_object* v_00_u03b2_193_, lean_object* v_a_194_, lean_object* v_x_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_197_, lean_object* v_a_198_, lean_object* v_x_199_){
_start:
{
uint8_t v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(v_00_u03b2_197_, v_a_198_, v_x_199_);
lean_dec(v_x_199_);
lean_dec(v_a_198_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(lean_object* v___x_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_202_);
lean_ctor_set(v___x_205_, 1, v___y_204_);
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0___boxed(lean_object* v___x_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(v___x_207_, v___y_208_, v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(lean_object* v_f_211_, lean_object* v_as_212_, size_t v_i_213_, size_t v_stop_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = lean_usize_dec_eq(v_i_213_, v_stop_214_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_array_uget_borrowed(v_as_212_, v_i_213_);
lean_inc_ref(v_f_211_);
lean_inc_ref(v___y_216_);
lean_inc(v___x_219_);
v___x_220_ = lean_apply_3(v_f_211_, v___x_219_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_dec_ref(v_f_211_);
return v___x_220_;
}
else
{
lean_object* v_a_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; size_t v___x_224_; size_t v___x_225_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v_fst_222_ = lean_ctor_get(v_a_221_, 0);
lean_inc(v_fst_222_);
v_snd_223_ = lean_ctor_get(v_a_221_, 1);
lean_inc(v_snd_223_);
lean_dec(v_a_221_);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_i_213_, v___x_224_);
v_i_213_ = v___x_225_;
v_b_215_ = v_fst_222_;
v___y_217_ = v_snd_223_;
goto _start;
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v_f_211_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_b_215_);
lean_ctor_set(v___x_227_, 1, v___y_217_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed(lean_object* v_f_229_, lean_object* v_as_230_, lean_object* v_i_231_, lean_object* v_stop_232_, lean_object* v_b_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
size_t v_i_boxed_236_; size_t v_stop_boxed_237_; lean_object* v_res_238_; 
v_i_boxed_236_ = lean_unbox_usize(v_i_231_);
lean_dec(v_i_231_);
v_stop_boxed_237_ = lean_unbox_usize(v_stop_232_);
lean_dec(v_stop_232_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_229_, v_as_230_, v_i_boxed_236_, v_stop_boxed_237_, v_b_233_, v___y_234_, v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec_ref(v_as_230_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(lean_object* v_f_239_, lean_object* v_as_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
if (lean_obj_tag(v_as_240_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_f_239_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___y_242_);
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v_head_246_; lean_object* v_tail_247_; lean_object* v___x_248_; 
v_head_246_ = lean_ctor_get(v_as_240_, 0);
lean_inc(v_head_246_);
v_tail_247_ = lean_ctor_get(v_as_240_, 1);
lean_inc(v_tail_247_);
lean_dec_ref_known(v_as_240_, 2);
lean_inc_ref(v_f_239_);
lean_inc_ref(v___y_241_);
v___x_248_ = lean_apply_3(v_f_239_, v_head_246_, v___y_241_, v___y_242_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_dec(v_tail_247_);
lean_dec_ref(v_f_239_);
return v___x_248_;
}
else
{
lean_object* v_a_249_; lean_object* v_snd_250_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v_snd_250_ = lean_ctor_get(v_a_249_, 1);
lean_inc(v_snd_250_);
lean_dec(v_a_249_);
v_as_240_ = v_tail_247_;
v___y_242_ = v_snd_250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1___boxed(lean_object* v_f_252_, lean_object* v_as_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_252_, v_as_253_, v___y_254_, v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(lean_object* v_f_257_, lean_object* v_as_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
if (lean_obj_tag(v_as_258_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_dec_ref(v_f_257_);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___y_260_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
else
{
lean_object* v_head_264_; lean_object* v_tail_265_; lean_object* v_ctor_266_; lean_object* v_rhs_267_; lean_object* v___x_268_; 
v_head_264_ = lean_ctor_get(v_as_258_, 0);
lean_inc(v_head_264_);
v_tail_265_ = lean_ctor_get(v_as_258_, 1);
lean_inc(v_tail_265_);
lean_dec_ref_known(v_as_258_, 2);
v_ctor_266_ = lean_ctor_get(v_head_264_, 0);
lean_inc(v_ctor_266_);
v_rhs_267_ = lean_ctor_get(v_head_264_, 2);
lean_inc_ref(v_rhs_267_);
lean_dec(v_head_264_);
lean_inc_ref(v_f_257_);
lean_inc_ref(v___y_259_);
v___x_268_ = lean_apply_3(v_f_257_, v_ctor_266_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_dec_ref(v_rhs_267_);
lean_dec(v_tail_265_);
lean_dec_ref(v_f_257_);
return v___x_268_;
}
else
{
lean_object* v_a_269_; lean_object* v_snd_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_268_, 1);
v_snd_270_ = lean_ctor_get(v_a_269_, 1);
lean_inc(v_snd_270_);
lean_dec(v_a_269_);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Lean_Expr_getUsedConstants(v_rhs_267_);
v___x_273_ = lean_array_get_size(v___x_272_);
v___x_274_ = lean_nat_dec_lt(v___x_271_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec_ref(v___x_272_);
v_as_258_ = v_tail_265_;
v___y_260_ = v_snd_270_;
goto _start;
}
else
{
lean_object* v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v___x_279_; 
v___x_276_ = lean_box(0);
v___x_277_ = ((size_t)0ULL);
v___x_278_ = lean_usize_of_nat(v___x_273_);
lean_inc_ref(v_f_257_);
v___x_279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_257_, v___x_272_, v___x_277_, v___x_278_, v___x_276_, v___y_259_, v_snd_270_);
lean_dec_ref(v___x_272_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_dec(v_tail_265_);
lean_dec_ref(v_f_257_);
return v___x_279_;
}
else
{
lean_object* v_a_280_; lean_object* v_snd_281_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_279_, 1);
v_snd_281_ = lean_ctor_get(v_a_280_, 1);
lean_inc(v_snd_281_);
lean_dec(v_a_280_);
v_as_258_ = v_tail_265_;
v___y_260_ = v_snd_281_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2___boxed(lean_object* v_f_283_, lean_object* v_as_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(v_f_283_, v_as_284_, v___y_285_, v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(lean_object* v_info_292_, lean_object* v_f_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___y_319_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_315_ = l_Lean_ConstantInfo_type(v_info_292_);
v___x_316_ = l_Lean_Expr_getUsedConstants(v___x_315_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_array_get_size(v___x_316_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_nat_dec_lt(v___x_317_, v___x_339_);
if (v___x_341_ == 0)
{
lean_object* v___f_342_; 
lean_dec_ref(v___x_316_);
v___f_342_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___closed__0));
v___y_319_ = v___f_342_;
goto v___jp_318_;
}
else
{
size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_usize_of_nat(v___x_339_);
v___x_344_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed__const__1));
v___x_345_ = lean_box_usize(v___x_343_);
lean_inc_ref(v_f_293_);
v___x_346_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed), 7, 5);
lean_closure_set(v___x_346_, 0, v_f_293_);
lean_closure_set(v___x_346_, 1, v___x_316_);
lean_closure_set(v___x_346_, 2, v___x_344_);
lean_closure_set(v___x_346_, 3, v___x_345_);
lean_closure_set(v___x_346_, 4, v___x_340_);
v___y_319_ = v___x_346_;
goto v___jp_318_;
}
v___jp_296_:
{
switch(lean_obj_tag(v_info_292_))
{
case 5:
{
lean_object* v_val_299_; lean_object* v_all_300_; lean_object* v_ctors_301_; lean_object* v___x_302_; 
v_val_299_ = lean_ctor_get(v_info_292_, 0);
lean_inc_ref(v_val_299_);
lean_dec_ref_known(v_info_292_, 1);
v_all_300_ = lean_ctor_get(v_val_299_, 3);
lean_inc(v_all_300_);
v_ctors_301_ = lean_ctor_get(v_val_299_, 4);
lean_inc(v_ctors_301_);
lean_dec_ref(v_val_299_);
lean_inc_ref(v_f_293_);
v___x_302_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_293_, v_ctors_301_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_dec(v_all_300_);
lean_dec_ref(v_f_293_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v_snd_304_; lean_object* v___x_305_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v_snd_304_ = lean_ctor_get(v_a_303_, 1);
lean_inc(v_snd_304_);
lean_dec(v_a_303_);
v___x_305_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_293_, v_all_300_, v___y_297_, v_snd_304_);
return v___x_305_;
}
}
case 6:
{
lean_object* v_val_306_; lean_object* v_induct_307_; lean_object* v___x_308_; 
v_val_306_ = lean_ctor_get(v_info_292_, 0);
lean_inc_ref(v_val_306_);
lean_dec_ref_known(v_info_292_, 1);
v_induct_307_ = lean_ctor_get(v_val_306_, 1);
lean_inc(v_induct_307_);
lean_dec_ref(v_val_306_);
lean_inc_ref(v___y_297_);
v___x_308_ = lean_apply_3(v_f_293_, v_induct_307_, v___y_297_, v___y_298_);
return v___x_308_;
}
case 7:
{
lean_object* v_val_309_; lean_object* v_rules_310_; lean_object* v___x_311_; 
v_val_309_ = lean_ctor_get(v_info_292_, 0);
lean_inc_ref(v_val_309_);
lean_dec_ref_known(v_info_292_, 1);
v_rules_310_ = lean_ctor_get(v_val_309_, 6);
lean_inc(v_rules_310_);
lean_dec_ref(v_val_309_);
v___x_311_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(v_f_293_, v_rules_310_, v___y_297_, v___y_298_);
return v___x_311_;
}
default: 
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v_f_293_);
lean_dec_ref(v_info_292_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___y_298_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
v___jp_318_:
{
lean_object* v___x_320_; 
lean_inc_ref(v___y_294_);
v___x_320_ = lean_apply_2(v___y_319_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_dec_ref(v_f_293_);
lean_dec_ref(v_info_292_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v_snd_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v_snd_322_ = lean_ctor_get(v_a_321_, 1);
lean_inc(v_snd_322_);
lean_dec(v_a_321_);
v___x_323_ = l_Lean_ConstantInfo_name(v_info_292_);
lean_inc_ref(v_f_293_);
lean_inc_ref(v___y_294_);
v___x_324_ = lean_apply_3(v_f_293_, v___x_323_, v___y_294_, v_snd_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_dec_ref(v_f_293_);
lean_dec_ref(v_info_292_);
return v___x_324_;
}
else
{
lean_object* v_a_325_; lean_object* v_snd_326_; uint8_t v___x_327_; lean_object* v___x_328_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v_snd_326_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_snd_326_);
lean_dec(v_a_325_);
v___x_327_ = 1;
lean_inc_ref(v_info_292_);
v___x_328_ = l_Lean_ConstantInfo_value_x3f(v_info_292_, v___x_327_);
if (lean_obj_tag(v___x_328_) == 1)
{
lean_object* v_val_329_; lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_val_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v___x_328_, 1);
v___x_330_ = l_Lean_Expr_getUsedConstants(v_val_329_);
v___x_331_ = lean_array_get_size(v___x_330_);
v___x_332_ = lean_nat_dec_lt(v___x_317_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_330_);
v___y_297_ = v___y_294_;
v___y_298_ = v_snd_326_;
goto v___jp_296_;
}
else
{
lean_object* v___x_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_333_ = lean_box(0);
v___x_334_ = ((size_t)0ULL);
v___x_335_ = lean_usize_of_nat(v___x_331_);
lean_inc_ref(v_f_293_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_293_, v___x_330_, v___x_334_, v___x_335_, v___x_333_, v___y_294_, v_snd_326_);
lean_dec_ref(v___x_330_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_dec_ref(v_f_293_);
lean_dec_ref(v_info_292_);
return v___x_336_;
}
else
{
lean_object* v_a_337_; lean_object* v_snd_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v_snd_338_ = lean_ctor_get(v_a_337_, 1);
lean_inc(v_snd_338_);
lean_dec(v_a_337_);
v___y_297_ = v___y_294_;
v___y_298_ = v_snd_338_;
goto v___jp_296_;
}
}
}
else
{
lean_dec(v___x_328_);
v___y_297_ = v___y_294_;
v___y_298_ = v_snd_326_;
goto v___jp_296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed(lean_object* v_info_347_, lean_object* v_f_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(v_info_347_, v_f_348_, v___y_349_, v___y_350_);
lean_dec_ref(v___y_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(lean_object* v_info_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___closed__0));
v___x_357_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(v_info_353_, v___x_356_, v_a_354_, v_a_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___boxed(lean_object* v_info_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_info_358_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(lean_object* v_a_362_, lean_object* v_x_363_){
_start:
{
if (lean_obj_tag(v_x_363_) == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
lean_object* v_key_365_; lean_object* v_value_366_; lean_object* v_tail_367_; uint8_t v___x_368_; 
v_key_365_ = lean_ctor_get(v_x_363_, 0);
v_value_366_ = lean_ctor_get(v_x_363_, 1);
v_tail_367_ = lean_ctor_get(v_x_363_, 2);
v___x_368_ = lean_name_eq(v_key_365_, v_a_362_);
if (v___x_368_ == 0)
{
v_x_363_ = v_tail_367_;
goto _start;
}
else
{
lean_object* v___x_370_; 
lean_inc(v_value_366_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_value_366_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg___boxed(lean_object* v_a_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec(v_a_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(lean_object* v_m_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_buckets_376_; lean_object* v___x_377_; uint64_t v___y_379_; 
v_buckets_376_ = lean_ctor_get(v_m_374_, 1);
v___x_377_ = lean_array_get_size(v_buckets_376_);
if (lean_obj_tag(v_a_375_) == 0)
{
uint64_t v___x_393_; 
v___x_393_ = 1723ULL;
v___y_379_ = v___x_393_;
goto v___jp_378_;
}
else
{
uint64_t v_hash_394_; 
v_hash_394_ = lean_ctor_get_uint64(v_a_375_, sizeof(void*)*2);
v___y_379_ = v_hash_394_;
goto v___jp_378_;
}
v___jp_378_:
{
uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v_fold_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; size_t v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_380_ = 32ULL;
v___x_381_ = lean_uint64_shift_right(v___y_379_, v___x_380_);
v_fold_382_ = lean_uint64_xor(v___y_379_, v___x_381_);
v___x_383_ = 16ULL;
v___x_384_ = lean_uint64_shift_right(v_fold_382_, v___x_383_);
v___x_385_ = lean_uint64_xor(v_fold_382_, v___x_384_);
v___x_386_ = lean_uint64_to_usize(v___x_385_);
v___x_387_ = lean_usize_of_nat(v___x_377_);
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_sub(v___x_387_, v___x_388_);
v___x_390_ = lean_usize_land(v___x_386_, v___x_389_);
v___x_391_ = lean_array_uget_borrowed(v_buckets_376_, v___x_390_);
v___x_392_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_375_, v___x_391_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg___boxed(lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_m_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
return v_x_398_;
}
else
{
lean_object* v_key_400_; lean_object* v_value_401_; lean_object* v_tail_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_428_; 
v_key_400_ = lean_ctor_get(v_x_399_, 0);
v_value_401_ = lean_ctor_get(v_x_399_, 1);
v_tail_402_ = lean_ctor_get(v_x_399_, 2);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_428_ == 0)
{
v___x_404_ = v_x_399_;
v_isShared_405_ = v_isSharedCheck_428_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_tail_402_);
lean_inc(v_value_401_);
lean_inc(v_key_400_);
lean_dec(v_x_399_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_428_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; uint64_t v___y_408_; 
v___x_406_ = lean_array_get_size(v_x_398_);
if (lean_obj_tag(v_key_400_) == 0)
{
uint64_t v___x_426_; 
v___x_426_ = 1723ULL;
v___y_408_ = v___x_426_;
goto v___jp_407_;
}
else
{
uint64_t v_hash_427_; 
v_hash_427_ = lean_ctor_get_uint64(v_key_400_, sizeof(void*)*2);
v___y_408_ = v_hash_427_;
goto v___jp_407_;
}
v___jp_407_:
{
uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v_fold_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_409_ = 32ULL;
v___x_410_ = lean_uint64_shift_right(v___y_408_, v___x_409_);
v_fold_411_ = lean_uint64_xor(v___y_408_, v___x_410_);
v___x_412_ = 16ULL;
v___x_413_ = lean_uint64_shift_right(v_fold_411_, v___x_412_);
v___x_414_ = lean_uint64_xor(v_fold_411_, v___x_413_);
v___x_415_ = lean_uint64_to_usize(v___x_414_);
v___x_416_ = lean_usize_of_nat(v___x_406_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_sub(v___x_416_, v___x_417_);
v___x_419_ = lean_usize_land(v___x_415_, v___x_418_);
v___x_420_ = lean_array_uget_borrowed(v_x_398_, v___x_419_);
lean_inc(v___x_420_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 2, v___x_420_);
v___x_422_ = v___x_404_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_key_400_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_value_401_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v___x_420_);
v___x_422_ = v_reuseFailAlloc_425_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = lean_array_uset(v_x_398_, v___x_419_, v___x_422_);
v_x_398_ = v___x_423_;
v_x_399_ = v_tail_402_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(lean_object* v_i_429_, lean_object* v_source_430_, lean_object* v_target_431_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_get_size(v_source_430_);
v___x_433_ = lean_nat_dec_lt(v_i_429_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_source_430_);
lean_dec(v_i_429_);
return v_target_431_;
}
else
{
lean_object* v_es_434_; lean_object* v___x_435_; lean_object* v_source_436_; lean_object* v_target_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_es_434_ = lean_array_fget(v_source_430_, v_i_429_);
v___x_435_ = lean_box(0);
v_source_436_ = lean_array_fset(v_source_430_, v_i_429_, v___x_435_);
v_target_437_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_target_431_, v_es_434_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_i_429_, v___x_438_);
lean_dec(v_i_429_);
v_i_429_ = v___x_439_;
v_source_430_ = v_source_436_;
v_target_431_ = v_target_437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(lean_object* v_data_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_nbuckets_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_442_ = lean_array_get_size(v_data_441_);
v___x_443_ = lean_unsigned_to_nat(2u);
v_nbuckets_444_ = lean_nat_mul(v___x_442_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_box(0);
v___x_447_ = lean_mk_array(v_nbuckets_444_, v___x_446_);
v___x_448_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v___x_445_, v_data_441_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(lean_object* v_m_449_, lean_object* v_a_450_, lean_object* v_b_451_){
_start:
{
lean_object* v_size_452_; lean_object* v_buckets_453_; lean_object* v___x_454_; uint64_t v___y_456_; 
v_size_452_ = lean_ctor_get(v_m_449_, 0);
v_buckets_453_ = lean_ctor_get(v_m_449_, 1);
v___x_454_ = lean_array_get_size(v_buckets_453_);
if (lean_obj_tag(v_a_450_) == 0)
{
uint64_t v___x_493_; 
v___x_493_ = 1723ULL;
v___y_456_ = v___x_493_;
goto v___jp_455_;
}
else
{
uint64_t v_hash_494_; 
v_hash_494_ = lean_ctor_get_uint64(v_a_450_, sizeof(void*)*2);
v___y_456_ = v_hash_494_;
goto v___jp_455_;
}
v___jp_455_:
{
uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v_fold_459_; uint64_t v___x_460_; uint64_t v___x_461_; uint64_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v_bkt_468_; uint8_t v___x_469_; 
v___x_457_ = 32ULL;
v___x_458_ = lean_uint64_shift_right(v___y_456_, v___x_457_);
v_fold_459_ = lean_uint64_xor(v___y_456_, v___x_458_);
v___x_460_ = 16ULL;
v___x_461_ = lean_uint64_shift_right(v_fold_459_, v___x_460_);
v___x_462_ = lean_uint64_xor(v_fold_459_, v___x_461_);
v___x_463_ = lean_uint64_to_usize(v___x_462_);
v___x_464_ = lean_usize_of_nat(v___x_454_);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_sub(v___x_464_, v___x_465_);
v___x_467_ = lean_usize_land(v___x_463_, v___x_466_);
v_bkt_468_ = lean_array_uget_borrowed(v_buckets_453_, v___x_467_);
v___x_469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_450_, v_bkt_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_490_; 
lean_inc_ref(v_buckets_453_);
lean_inc(v_size_452_);
v_isSharedCheck_490_ = !lean_is_exclusive(v_m_449_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; lean_object* v_unused_492_; 
v_unused_491_ = lean_ctor_get(v_m_449_, 1);
lean_dec(v_unused_491_);
v_unused_492_ = lean_ctor_get(v_m_449_, 0);
lean_dec(v_unused_492_);
v___x_471_ = v_m_449_;
v_isShared_472_ = v_isSharedCheck_490_;
goto v_resetjp_470_;
}
else
{
lean_dec(v_m_449_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_490_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v_size_x27_474_; lean_object* v___x_475_; lean_object* v_buckets_x27_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_473_ = lean_unsigned_to_nat(1u);
v_size_x27_474_ = lean_nat_add(v_size_452_, v___x_473_);
lean_dec(v_size_452_);
lean_inc(v_bkt_468_);
v___x_475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_475_, 0, v_a_450_);
lean_ctor_set(v___x_475_, 1, v_b_451_);
lean_ctor_set(v___x_475_, 2, v_bkt_468_);
v_buckets_x27_476_ = lean_array_uset(v_buckets_453_, v___x_467_, v___x_475_);
v___x_477_ = lean_unsigned_to_nat(4u);
v___x_478_ = lean_nat_mul(v_size_x27_474_, v___x_477_);
v___x_479_ = lean_unsigned_to_nat(3u);
v___x_480_ = lean_nat_div(v___x_478_, v___x_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_array_get_size(v_buckets_x27_476_);
v___x_482_ = lean_nat_dec_le(v___x_480_, v___x_481_);
lean_dec(v___x_480_);
if (v___x_482_ == 0)
{
lean_object* v_val_483_; lean_object* v___x_485_; 
v_val_483_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_buckets_x27_476_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v_val_483_);
lean_ctor_set(v___x_471_, 0, v_size_x27_474_);
v___x_485_ = v___x_471_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_size_x27_474_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v_val_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_488_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v_buckets_x27_476_);
lean_ctor_set(v___x_471_, 0, v_size_x27_474_);
v___x_488_ = v___x_471_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_size_x27_474_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_buckets_x27_476_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_dec(v_b_451_);
lean_dec(v_a_450_);
return v_m_449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
lean_inc(v___x_501_);
v___x_502_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(v___x_501_, v___y_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
return v___x_502_;
}
else
{
lean_object* v_a_503_; lean_object* v_fst_504_; lean_object* v_snd_505_; size_t v___x_506_; size_t v___x_507_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v_fst_504_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_fst_504_);
v_snd_505_ = lean_ctor_get(v_a_503_, 1);
lean_inc(v_snd_505_);
lean_dec(v_a_503_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_add(v_i_496_, v___x_506_);
v_i_496_ = v___x_507_;
v_b_498_ = v_fst_504_;
v___y_499_ = v_snd_505_;
goto _start;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_b_498_);
lean_ctor_set(v___x_509_, 1, v___y_499_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg___boxed(lean_object* v_as_511_, lean_object* v_i_512_, lean_object* v_stop_513_, lean_object* v_b_514_, lean_object* v___y_515_){
_start:
{
size_t v_i_boxed_516_; size_t v_stop_boxed_517_; lean_object* v_res_518_; 
v_i_boxed_516_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_stop_boxed_517_ = lean_unbox_usize(v_stop_513_);
lean_dec(v_stop_513_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_511_, v_i_boxed_516_, v_stop_boxed_517_, v_b_514_, v___y_515_);
lean_dec_ref(v_as_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_worklist_525_; lean_object* v_checked_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_worklist_525_ = lean_ctor_get(v_a_524_, 0);
v_checked_526_ = lean_ctor_get(v_a_524_, 1);
v___x_527_ = lean_array_get_size(v_worklist_525_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_nat_dec_eq(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_623_; 
lean_inc_ref(v_checked_526_);
lean_inc_ref(v_worklist_525_);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_524_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; lean_object* v_unused_625_; 
v_unused_624_ = lean_ctor_get(v_a_524_, 1);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_a_524_, 0);
lean_dec(v_unused_625_);
v___x_531_ = v_a_524_;
v_isShared_532_ = v_isSharedCheck_623_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_a_524_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_623_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___y_538_; lean_object* v_worklist_539_; lean_object* v_checked_540_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_553_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_sub(v___x_527_, v___x_534_);
v___x_536_ = lean_array_get(v___x_533_, v_worklist_525_, v___x_535_);
lean_dec(v___x_535_);
v___x_556_ = lean_array_pop(v_worklist_525_);
lean_inc_ref(v_checked_526_);
lean_inc_ref(v___x_556_);
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v_checked_526_);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_526_, v___x_536_);
if (v___x_558_ == 0)
{
lean_object* v_challenge_559_; lean_object* v_solution_560_; lean_object* v_definitionTargets_561_; lean_object* v_theoremTargets_562_; lean_object* v_constMap_563_; lean_object* v___x_564_; 
v_challenge_559_ = lean_ctor_get(v_a_523_, 0);
v_solution_560_ = lean_ctor_get(v_a_523_, 1);
v_definitionTargets_561_ = lean_ctor_get(v_a_523_, 2);
v_theoremTargets_562_ = lean_ctor_get(v_a_523_, 3);
v_constMap_563_ = lean_ctor_get(v_challenge_559_, 0);
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_563_, v___x_536_);
if (lean_obj_tag(v___x_564_) == 1)
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_614_; 
v_val_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_614_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_614_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_614_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_constMap_569_; lean_object* v___x_570_; 
v_constMap_569_ = lean_ctor_get(v_solution_560_, 0);
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_569_, v___x_536_);
if (lean_obj_tag(v___x_570_) == 1)
{
lean_object* v_val_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_567_);
v_val_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_604_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_604_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_val_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_604_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = l_Lean_ConstantInfo_name(v_val_571_);
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_definitionTargets_561_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_theoremTargets_562_, v___x_588_);
lean_dec(v___x_588_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
lean_dec_ref(v___x_556_);
lean_dec_ref(v_checked_526_);
v___x_591_ = l_Lake_Check_Compare_instBEqConstantInfo__lake_beq(v_val_565_, v_val_571_);
lean_dec(v_val_565_);
if (v___x_591_ == 0)
{
uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
lean_dec(v_val_571_);
lean_dec_ref_known(v___x_557_, 2);
lean_del_object(v___x_531_);
v___x_592_ = 1;
v___x_593_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
v___x_594_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_536_, v___x_592_);
v___x_595_ = lean_string_append(v___x_593_, v___x_594_);
lean_dec_ref(v___x_594_);
v___x_596_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_597_ = lean_string_append(v___x_595_, v___x_596_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 0);
lean_ctor_set(v___x_573_, 0, v___x_597_);
v___x_599_ = v___x_573_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_601_; 
lean_del_object(v___x_573_);
v___x_601_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_val_571_, v_a_523_, v___x_557_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_dec(v___x_536_);
lean_del_object(v___x_531_);
return v___x_601_;
}
else
{
lean_object* v_a_602_; lean_object* v_snd_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v_snd_603_ = lean_ctor_get(v_a_602_, 1);
lean_inc(v_snd_603_);
lean_dec(v_a_602_);
v___y_548_ = v_a_523_;
v___y_549_ = v_snd_603_;
goto v___jp_547_;
}
}
}
else
{
lean_del_object(v___x_573_);
lean_dec(v_val_565_);
goto v___jp_575_;
}
}
else
{
lean_dec(v___x_588_);
lean_del_object(v___x_573_);
lean_dec(v_val_565_);
goto v___jp_575_;
}
v___jp_575_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_576_ = l_Lean_ConstantInfo_type(v_val_571_);
lean_dec(v_val_571_);
v___x_577_ = l_Lean_Expr_getUsedConstants(v___x_576_);
v___x_578_ = lean_array_get_size(v___x_577_);
v___x_579_ = lean_nat_dec_lt(v___x_528_, v___x_578_);
if (v___x_579_ == 0)
{
lean_dec_ref(v___x_577_);
lean_dec_ref_known(v___x_557_, 2);
v___y_538_ = v_a_523_;
v_worklist_539_ = v___x_556_;
v_checked_540_ = v_checked_526_;
goto v___jp_537_;
}
else
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_box(0);
v___x_581_ = lean_nat_dec_le(v___x_578_, v___x_578_);
if (v___x_581_ == 0)
{
if (v___x_579_ == 0)
{
lean_dec_ref(v___x_577_);
lean_dec_ref_known(v___x_557_, 2);
v___y_538_ = v_a_523_;
v_worklist_539_ = v___x_556_;
v_checked_540_ = v_checked_526_;
goto v___jp_537_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v___x_556_);
lean_dec_ref(v_checked_526_);
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_578_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_577_, v___x_582_, v___x_583_, v___x_580_, v___x_557_);
lean_dec_ref(v___x_577_);
v___y_553_ = v___x_584_;
goto v___jp_552_;
}
}
else
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
lean_dec_ref(v___x_556_);
lean_dec_ref(v_checked_526_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_578_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_577_, v___x_585_, v___x_586_, v___x_580_, v___x_557_);
lean_dec_ref(v___x_577_);
v___y_553_ = v___x_587_;
goto v___jp_552_;
}
}
}
}
}
else
{
lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
lean_dec(v___x_570_);
lean_dec(v_val_565_);
lean_dec_ref_known(v___x_557_, 2);
lean_dec_ref(v___x_556_);
lean_del_object(v___x_531_);
lean_dec_ref(v_checked_526_);
v___x_605_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2));
v___x_606_ = 1;
v___x_607_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_536_, v___x_606_);
v___x_608_ = lean_string_append(v___x_605_, v___x_607_);
lean_dec_ref(v___x_607_);
v___x_609_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_610_ = lean_string_append(v___x_608_, v___x_609_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 0);
lean_ctor_set(v___x_567_, 0, v___x_610_);
v___x_612_ = v___x_567_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v___x_564_);
lean_dec_ref_known(v___x_557_, 2);
lean_dec_ref(v___x_556_);
lean_del_object(v___x_531_);
lean_dec_ref(v_checked_526_);
v___x_615_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3));
v___x_616_ = 1;
v___x_617_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_536_, v___x_616_);
v___x_618_ = lean_string_append(v___x_615_, v___x_617_);
lean_dec_ref(v___x_617_);
v___x_619_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
else
{
lean_dec_ref(v___x_556_);
lean_dec(v___x_536_);
lean_del_object(v___x_531_);
lean_dec_ref(v_checked_526_);
v_a_524_ = v___x_557_;
goto _start;
}
v___jp_537_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_box(0);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_checked_540_, v___x_536_, v___x_541_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_542_);
lean_ctor_set(v___x_531_, 0, v_worklist_539_);
v___x_544_ = v___x_531_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_worklist_539_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v_a_523_ = v___y_538_;
v_a_524_ = v___x_544_;
goto _start;
}
}
v___jp_547_:
{
lean_object* v_worklist_550_; lean_object* v_checked_551_; 
v_worklist_550_ = lean_ctor_get(v___y_549_, 0);
lean_inc_ref(v_worklist_550_);
v_checked_551_ = lean_ctor_get(v___y_549_, 1);
lean_inc_ref(v_checked_551_);
lean_dec_ref(v___y_549_);
v___y_538_ = v___y_548_;
v_worklist_539_ = v_worklist_550_;
v_checked_540_ = v_checked_551_;
goto v___jp_537_;
}
v___jp_552_:
{
if (lean_obj_tag(v___y_553_) == 0)
{
lean_dec(v___x_536_);
lean_del_object(v___x_531_);
return v___y_553_;
}
else
{
lean_object* v_a_554_; lean_object* v_snd_555_; 
v_a_554_ = lean_ctor_get(v___y_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v___y_553_, 1);
v_snd_555_ = lean_ctor_get(v_a_554_, 1);
lean_inc(v_snd_555_);
lean_dec(v_a_554_);
v___y_548_ = v_a_523_;
v___y_549_ = v_snd_555_;
goto v___jp_547_;
}
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v_a_524_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___boxed(lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v_a_629_, v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0(lean_object* v_00_u03b2_632_, lean_object* v_m_633_, lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_m_633_, v_a_634_, v_b_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(lean_object* v_00_u03b2_637_, lean_object* v_m_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_638_, v_a_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___boxed(lean_object* v_00_u03b2_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(v_00_u03b2_641_, v_m_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_m_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(lean_object* v_as_645_, size_t v_i_646_, size_t v_stop_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_645_, v_i_646_, v_stop_647_, v_b_648_, v___y_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___boxed(lean_object* v_as_652_, lean_object* v_i_653_, lean_object* v_stop_654_, lean_object* v_b_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_i_boxed_658_; size_t v_stop_boxed_659_; lean_object* v_res_660_; 
v_i_boxed_658_ = lean_unbox_usize(v_i_653_);
lean_dec(v_i_653_);
v_stop_boxed_659_ = lean_unbox_usize(v_stop_654_);
lean_dec(v_stop_654_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(v_as_652_, v_i_boxed_658_, v_stop_boxed_659_, v_b_655_, v___y_656_, v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v_as_652_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0(lean_object* v_00_u03b2_661_, lean_object* v_data_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_data_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(lean_object* v_00_u03b2_664_, lean_object* v_a_665_, lean_object* v_x_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___boxed(lean_object* v_00_u03b2_668_, lean_object* v_a_669_, lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(v_00_u03b2_668_, v_a_669_, v_x_670_);
lean_dec(v_x_670_);
lean_dec(v_a_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_672_, lean_object* v_i_673_, lean_object* v_source_674_, lean_object* v_target_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v_i_673_, v_source_674_, v_target_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_x_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT uint8_t l_Lake_Check_definitionHoleMatches(lean_object* v_challengeHole_681_, lean_object* v_solutionHole_682_){
_start:
{
lean_object* v_toConstantVal_683_; uint8_t v_safety_684_; lean_object* v_toConstantVal_685_; uint8_t v_safety_686_; uint8_t v___x_687_; 
v_toConstantVal_683_ = lean_ctor_get(v_challengeHole_681_, 0);
v_safety_684_ = lean_ctor_get_uint8(v_challengeHole_681_, sizeof(void*)*4);
v_toConstantVal_685_ = lean_ctor_get(v_solutionHole_682_, 0);
v_safety_686_ = lean_ctor_get_uint8(v_solutionHole_682_, sizeof(void*)*4);
v___x_687_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_683_, v_toConstantVal_685_);
if (v___x_687_ == 0)
{
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_684_, v_safety_686_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_definitionHoleMatches___boxed(lean_object* v_challengeHole_689_, lean_object* v_solutionHole_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lake_Check_definitionHoleMatches(v_challengeHole_689_, v_solutionHole_690_);
lean_dec_ref(v_solutionHole_690_);
lean_dec_ref(v_challengeHole_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(lean_object* v_as_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_b_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_697_ == 0)
{
return v_b_696_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_699_; lean_object* v_r_700_; size_t v___x_701_; size_t v___x_702_; 
v_a_698_ = lean_array_uget_borrowed(v_as_693_, v_i_695_);
v___x_699_ = lean_box(0);
lean_inc(v_a_698_);
v_r_700_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_b_696_, v_a_698_, v___x_699_);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_add(v_i_695_, v___x_701_);
v_i_695_ = v___x_702_;
v_b_696_ = v_r_700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2___boxed(lean_object* v_as_704_, lean_object* v_sz_705_, lean_object* v_i_706_, lean_object* v_b_707_){
_start:
{
size_t v_sz_boxed_708_; size_t v_i_boxed_709_; lean_object* v_res_710_; 
v_sz_boxed_708_ = lean_unbox_usize(v_sz_705_);
lean_dec(v_sz_705_);
v_i_boxed_709_ = lean_unbox_usize(v_i_706_);
lean_dec(v_i_706_);
v_res_710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_as_704_, v_sz_boxed_708_, v_i_boxed_709_, v_b_707_);
lean_dec_ref(v_as_704_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(lean_object* v_m_711_, lean_object* v_l_712_){
_start:
{
size_t v_sz_713_; size_t v___x_714_; lean_object* v___x_715_; 
v_sz_713_ = lean_array_size(v_l_712_);
v___x_714_ = ((size_t)0ULL);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_l_712_, v_sz_713_, v___x_714_, v_m_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2___boxed(lean_object* v_m_716_, lean_object* v_l_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v_m_716_, v_l_717_);
lean_dec_ref(v_l_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(lean_object* v_challenge_723_, lean_object* v_solution_724_, lean_object* v_as_725_, size_t v_sz_726_, size_t v_i_727_, lean_object* v_b_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = lean_usize_dec_lt(v_i_727_, v_sz_726_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_728_);
return v___x_730_;
}
else
{
lean_object* v_constMap_731_; lean_object* v_a_732_; lean_object* v___x_733_; 
v_constMap_731_ = lean_ctor_get(v_challenge_723_, 0);
v_a_732_ = lean_array_uget_borrowed(v_as_725_, v_i_727_);
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_731_, v_a_732_);
if (lean_obj_tag(v___x_733_) == 1)
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_796_; 
v_val_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_796_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_796_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_796_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_constMap_738_; lean_object* v___x_739_; 
v_constMap_738_ = lean_ctor_get(v_solution_724_, 0);
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_738_, v_a_732_);
if (lean_obj_tag(v___x_739_) == 1)
{
lean_del_object(v___x_736_);
if (lean_obj_tag(v_val_734_) == 1)
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
if (lean_obj_tag(v_val_740_) == 1)
{
lean_object* v_val_741_; lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_761_; 
v_val_741_ = lean_ctor_get(v_val_734_, 0);
lean_inc_ref(v_val_741_);
lean_dec_ref_known(v_val_734_, 1);
v_val_742_ = lean_ctor_get(v_val_740_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_val_740_);
if (v_isSharedCheck_761_ == 0)
{
v___x_744_ = v_val_740_;
v_isShared_745_ = v_isSharedCheck_761_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v_val_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_761_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint8_t v___x_746_; 
v___x_746_ = l_Lake_Check_definitionHoleMatches(v_val_741_, v_val_742_);
lean_dec_ref(v_val_741_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec_ref(v_val_742_);
lean_dec_ref(v_b_728_);
v___x_747_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
lean_inc(v_a_732_);
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_732_, v___x_729_);
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 0);
lean_ctor_set(v___x_744_, 0, v___x_751_);
v___x_753_ = v___x_744_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v_toConstantVal_755_; lean_object* v_name_756_; lean_object* v___x_757_; size_t v___x_758_; size_t v___x_759_; 
lean_del_object(v___x_744_);
v_toConstantVal_755_ = lean_ctor_get(v_val_742_, 0);
lean_inc_ref(v_toConstantVal_755_);
lean_dec_ref(v_val_742_);
v_name_756_ = lean_ctor_get(v_toConstantVal_755_, 0);
lean_inc(v_name_756_);
lean_dec_ref(v_toConstantVal_755_);
v___x_757_ = lean_array_push(v_b_728_, v_name_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_727_, v___x_758_);
v_i_727_ = v___x_759_;
v_b_728_ = v___x_757_;
goto _start;
}
}
}
else
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_val_740_);
lean_dec_ref(v_b_728_);
v_isSharedCheck_773_ = !lean_is_exclusive(v_val_734_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_val_734_, 0);
lean_dec(v_unused_774_);
v___x_763_ = v_val_734_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_val_734_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0));
lean_inc(v_a_732_);
v___x_766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_732_, v___x_729_);
v___x_767_ = lean_string_append(v___x_765_, v___x_766_);
lean_dec_ref(v___x_766_);
v___x_768_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_769_ = lean_string_append(v___x_767_, v___x_768_);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 0);
lean_ctor_set(v___x_763_, 0, v___x_769_);
v___x_771_ = v___x_763_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_val_734_);
lean_dec_ref(v_b_728_);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_739_, 0);
lean_dec(v_unused_787_);
v___x_776_ = v___x_739_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_739_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1));
lean_inc(v_a_732_);
v___x_779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_732_, v___x_729_);
v___x_780_ = lean_string_append(v___x_778_, v___x_779_);
lean_dec_ref(v___x_779_);
v___x_781_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_782_ = lean_string_append(v___x_780_, v___x_781_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 0);
lean_ctor_set(v___x_776_, 0, v___x_782_);
v___x_784_ = v___x_776_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
lean_dec(v___x_739_);
lean_dec(v_val_734_);
lean_dec_ref(v_b_728_);
v___x_788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_732_);
v___x_789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_732_, v___x_729_);
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
lean_dec_ref(v___x_789_);
v___x_791_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_792_ = lean_string_append(v___x_790_, v___x_791_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v___x_792_);
v___x_794_ = v___x_736_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec(v___x_733_);
lean_dec_ref(v_b_728_);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_732_);
v___x_798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_732_, v___x_729_);
v___x_799_ = lean_string_append(v___x_797_, v___x_798_);
lean_dec_ref(v___x_798_);
v___x_800_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_801_ = lean_string_append(v___x_799_, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___boxed(lean_object* v_challenge_803_, lean_object* v_solution_804_, lean_object* v_as_805_, lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_b_808_){
_start:
{
size_t v_sz_boxed_809_; size_t v_i_boxed_810_; lean_object* v_res_811_; 
v_sz_boxed_809_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_810_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_803_, v_solution_804_, v_as_805_, v_sz_boxed_809_, v_i_boxed_810_, v_b_808_);
lean_dec_ref(v_as_805_);
lean_dec_ref(v_solution_804_);
lean_dec_ref(v_challenge_803_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(lean_object* v_challenge_814_, lean_object* v_solution_815_, lean_object* v_as_816_, size_t v_sz_817_, size_t v_i_818_, lean_object* v_b_819_){
_start:
{
uint8_t v___x_820_; 
v___x_820_ = lean_usize_dec_lt(v_i_818_, v_sz_817_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_b_819_);
return v___x_821_;
}
else
{
lean_object* v_constMap_822_; lean_object* v_a_823_; lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_847_; 
v_constMap_822_ = lean_ctor_get(v_challenge_814_, 0);
v_a_823_ = lean_array_uget_borrowed(v_as_816_, v_i_818_);
v___x_847_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_822_, v_a_823_);
if (lean_obj_tag(v___x_847_) == 1)
{
lean_object* v_val_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_872_; 
v_val_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_872_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_872_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_val_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_872_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_constMap_852_; lean_object* v___x_853_; 
v_constMap_852_ = lean_ctor_get(v_solution_815_, 0);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_852_, v_a_823_);
if (lean_obj_tag(v___x_853_) == 1)
{
lean_del_object(v___x_850_);
switch(lean_obj_tag(v_val_848_))
{
case 2:
{
lean_object* v_val_854_; 
v_val_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_854_);
lean_dec_ref_known(v___x_853_, 1);
if (lean_obj_tag(v_val_854_) == 2)
{
lean_object* v_val_855_; lean_object* v_val_856_; lean_object* v_toConstantVal_857_; lean_object* v_toConstantVal_858_; 
v_val_855_ = lean_ctor_get(v_val_848_, 0);
lean_inc_ref(v_val_855_);
lean_dec_ref_known(v_val_848_, 1);
v_val_856_ = lean_ctor_get(v_val_854_, 0);
lean_inc_ref(v_val_856_);
lean_dec_ref_known(v_val_854_, 1);
v_toConstantVal_857_ = lean_ctor_get(v_val_855_, 0);
lean_inc_ref(v_toConstantVal_857_);
lean_dec_ref(v_val_855_);
v_toConstantVal_858_ = lean_ctor_get(v_val_856_, 0);
lean_inc_ref(v_toConstantVal_858_);
lean_dec_ref(v_val_856_);
v_fst_832_ = v_toConstantVal_857_;
v_snd_833_ = v_toConstantVal_858_;
goto v___jp_831_;
}
else
{
lean_dec(v_val_854_);
lean_dec_ref_known(v_val_848_, 1);
lean_dec_ref(v_b_819_);
goto v___jp_824_;
}
}
case 0:
{
lean_object* v_val_859_; 
v_val_859_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_859_);
lean_dec_ref_known(v___x_853_, 1);
if (lean_obj_tag(v_val_859_) == 0)
{
lean_object* v_val_860_; lean_object* v_val_861_; lean_object* v_toConstantVal_862_; lean_object* v_toConstantVal_863_; 
v_val_860_ = lean_ctor_get(v_val_848_, 0);
lean_inc_ref(v_val_860_);
lean_dec_ref_known(v_val_848_, 1);
v_val_861_ = lean_ctor_get(v_val_859_, 0);
lean_inc_ref(v_val_861_);
lean_dec_ref_known(v_val_859_, 1);
v_toConstantVal_862_ = lean_ctor_get(v_val_860_, 0);
lean_inc_ref(v_toConstantVal_862_);
lean_dec_ref(v_val_860_);
v_toConstantVal_863_ = lean_ctor_get(v_val_861_, 0);
lean_inc_ref(v_toConstantVal_863_);
lean_dec_ref(v_val_861_);
v_fst_832_ = v_toConstantVal_862_;
v_snd_833_ = v_toConstantVal_863_;
goto v___jp_831_;
}
else
{
lean_dec_ref_known(v_val_848_, 1);
lean_dec(v_val_859_);
lean_dec_ref(v_b_819_);
goto v___jp_824_;
}
}
default: 
{
lean_dec_ref_known(v___x_853_, 1);
lean_dec(v_val_848_);
lean_dec_ref(v_b_819_);
goto v___jp_824_;
}
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v___x_853_);
lean_dec(v_val_848_);
lean_dec_ref(v_b_819_);
v___x_864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_823_);
v___x_865_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_823_, v___x_820_);
v___x_866_ = lean_string_append(v___x_864_, v___x_865_);
lean_dec_ref(v___x_865_);
v___x_867_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_868_ = lean_string_append(v___x_866_, v___x_867_);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 0);
lean_ctor_set(v___x_850_, 0, v___x_868_);
v___x_870_ = v___x_850_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v___x_847_);
lean_dec_ref(v_b_819_);
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_823_);
v___x_874_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_823_, v___x_820_);
v___x_875_ = lean_string_append(v___x_873_, v___x_874_);
lean_dec_ref(v___x_874_);
v___x_876_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_877_ = lean_string_append(v___x_875_, v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
v___jp_824_:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0));
lean_inc(v_a_823_);
v___x_826_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_823_, v___x_820_);
v___x_827_ = lean_string_append(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
v___x_828_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
return v___x_830_;
}
v___jp_831_:
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_instBEqConstantVal_beq(v_fst_832_, v_snd_833_);
lean_dec_ref(v_snd_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v_fst_832_);
lean_dec_ref(v_b_819_);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1));
lean_inc(v_a_823_);
v___x_836_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_823_, v___x_820_);
v___x_837_ = lean_string_append(v___x_835_, v___x_836_);
lean_dec_ref(v___x_836_);
v___x_838_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_839_ = lean_string_append(v___x_837_, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
else
{
lean_object* v_type_841_; lean_object* v___x_842_; lean_object* v___x_843_; size_t v___x_844_; size_t v___x_845_; 
v_type_841_ = lean_ctor_get(v_fst_832_, 2);
lean_inc_ref(v_type_841_);
lean_dec_ref(v_fst_832_);
v___x_842_ = l_Lean_Expr_getUsedConstants(v_type_841_);
v___x_843_ = l_Array_append___redArg(v_b_819_, v___x_842_);
lean_dec_ref(v___x_842_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_818_, v___x_844_);
v_i_818_ = v___x_845_;
v_b_819_ = v___x_843_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___boxed(lean_object* v_challenge_879_, lean_object* v_solution_880_, lean_object* v_as_881_, lean_object* v_sz_882_, lean_object* v_i_883_, lean_object* v_b_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_882_);
lean_dec(v_sz_882_);
v_i_boxed_886_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_879_, v_solution_880_, v_as_881_, v_sz_boxed_885_, v_i_boxed_886_, v_b_884_);
lean_dec_ref(v_as_881_);
lean_dec_ref(v_solution_880_);
lean_dec_ref(v_challenge_879_);
return v_res_887_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__0(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
v___x_889_ = lean_unsigned_to_nat(16u);
v___x_890_ = lean_mk_array(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__1(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_obj_once(&l_Lake_Check_compareAt___closed__0, &l_Lake_Check_compareAt___closed__0_once, _init_l_Lake_Check_compareAt___closed__0);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___x_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt(lean_object* v_challenge_894_, lean_object* v_solution_895_, lean_object* v_theoremTargets_896_, lean_object* v_definitionTargets_897_, lean_object* v_primitive_898_){
_start:
{
size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; 
v_sz_899_ = lean_array_size(v_theoremTargets_896_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_894_, v_solution_895_, v_theoremTargets_896_, v_sz_899_, v___x_900_, v_primitive_898_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_solution_895_);
lean_dec_ref(v_challenge_894_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; size_t v_sz_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_901_, 1);
v_sz_911_ = lean_array_size(v_definitionTargets_897_);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_894_, v_solution_895_, v_definitionTargets_897_, v_sz_911_, v___x_900_, v_a_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_solution_895_);
lean_dec_ref(v_challenge_894_);
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_a_921_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_912_, 1);
v___x_922_ = lean_obj_once(&l_Lake_Check_compareAt___closed__1, &l_Lake_Check_compareAt___closed__1_once, _init_l_Lake_Check_compareAt___closed__1);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_922_, v_definitionTargets_897_);
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_922_, v_theoremTargets_896_);
v___x_925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_925_, 0, v_challenge_894_);
lean_ctor_set(v___x_925_, 1, v_solution_895_);
lean_ctor_set(v___x_925_, 2, v___x_923_);
lean_ctor_set(v___x_925_, 3, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_a_921_);
lean_ctor_set(v___x_926_, 1, v___x_922_);
v___x_927_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v___x_925_, v___x_926_);
lean_dec_ref_known(v___x_925_, 4);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_a_936_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_944_ == 0)
{
v___x_938_ = v___x_927_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_927_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_fst_940_; lean_object* v___x_942_; 
v_fst_940_ = lean_ctor_get(v_a_936_, 0);
lean_inc(v_fst_940_);
lean_dec(v_a_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v_fst_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_fst_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt___boxed(lean_object* v_challenge_945_, lean_object* v_solution_946_, lean_object* v_theoremTargets_947_, lean_object* v_definitionTargets_948_, lean_object* v_primitive_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lake_Check_compareAt(v_challenge_945_, v_solution_946_, v_theoremTargets_947_, v_definitionTargets_948_, v_primitive_949_);
lean_dec_ref(v_definitionTargets_948_);
lean_dec_ref(v_theoremTargets_947_);
return v_res_950_;
}
}
lean_object* runtime_initialize_LeanExport_Parse(uint8_t builtin);
lean_object* runtime_initialize_Lake_Check_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Check_Compare(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_LeanExport_Parse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Check_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Check_Compare(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_LeanExport_Parse(uint8_t builtin);
lean_object* initialize_Lake_Check_Util(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Check_Compare(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_LeanExport_Parse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Check_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Check_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Check_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Check_Compare(builtin);
}
#ifdef __cplusplus
}
#endif
