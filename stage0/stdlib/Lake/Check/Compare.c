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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqConstantInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_instBEqConstantVal_beq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = lean_name_eq(v_key_4_, v_a_1_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg___boxed(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_buckets_15_; lean_object* v___x_16_; uint64_t v___y_18_; 
v_buckets_15_ = lean_ctor_get(v_m_13_, 1);
v___x_16_ = lean_array_get_size(v_buckets_15_);
if (lean_obj_tag(v_a_14_) == 0)
{
uint64_t v___x_32_; 
v___x_32_ = 1723ULL;
v___y_18_ = v___x_32_;
goto v___jp_17_;
}
else
{
uint64_t v_hash_33_; 
v_hash_33_ = lean_ctor_get_uint64(v_a_14_, sizeof(void*)*2);
v___y_18_ = v_hash_33_;
goto v___jp_17_;
}
v___jp_17_:
{
uint64_t v___x_19_; uint64_t v___x_20_; uint64_t v_fold_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; size_t v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_19_ = 32ULL;
v___x_20_ = lean_uint64_shift_right(v___y_18_, v___x_19_);
v_fold_21_ = lean_uint64_xor(v___y_18_, v___x_20_);
v___x_22_ = 16ULL;
v___x_23_ = lean_uint64_shift_right(v_fold_21_, v___x_22_);
v___x_24_ = lean_uint64_xor(v_fold_21_, v___x_23_);
v___x_25_ = lean_uint64_to_usize(v___x_24_);
v___x_26_ = lean_usize_of_nat(v___x_16_);
v___x_27_ = ((size_t)1ULL);
v___x_28_ = lean_usize_sub(v___x_26_, v___x_27_);
v___x_29_ = lean_usize_land(v___x_25_, v___x_28_);
v___x_30_ = lean_array_uget_borrowed(v_buckets_15_, v___x_29_);
v___x_31_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_14_, v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_13_ = stack[0].m_obj;
lean_object* v_a_14_ = stack[1].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_13_, v_a_14_);
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg___boxed(lean_object* v_m_35_, lean_object* v_a_36_){
_start:
{
uint8_t v_res_37_; lean_object* v_r_38_; 
v_res_37_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_35_, v_a_36_);
lean_dec(v_a_36_);
lean_dec_ref(v_m_35_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(lean_object* v_n_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_worklist_41_; lean_object* v_checked_42_; uint8_t v___x_43_; 
v_worklist_41_ = lean_ctor_get(v_a_40_, 0);
v_checked_42_ = lean_ctor_get(v_a_40_, 1);
v___x_43_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_42_, v_n_39_);
if (v___x_43_ == 0)
{
lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_54_; 
lean_inc_ref(v_checked_42_);
lean_inc_ref(v_worklist_41_);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_40_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; lean_object* v_unused_56_; 
v_unused_55_ = lean_ctor_get(v_a_40_, 1);
lean_dec(v_unused_55_);
v_unused_56_ = lean_ctor_get(v_a_40_, 0);
lean_dec(v_unused_56_);
v___x_45_ = v_a_40_;
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
else
{
lean_dec(v_a_40_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_47_ = lean_box(0);
v___x_48_ = lean_array_push(v_worklist_41_, v_n_39_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_48_);
v___x_50_ = v___x_45_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_checked_42_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_47_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_n_39_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v_a_40_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(lean_object* v_n_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(v_n_60_, v_a_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___boxed(lean_object* v_n_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(v_n_64_, v_a_65_, v_a_66_);
lean_dec_ref(v_a_65_);
return v_res_67_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(lean_object* v_00_u03b2_68_, lean_object* v_m_69_, lean_object* v_a_70_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_69_, v_a_70_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_69_ = stack[1].m_obj;
lean_object* v_a_70_ = stack[2].m_obj;
uint8_t v_res_72_;
v_res_72_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(lean_box(0), v_m_69_, v_a_70_);
stack->m_num = v_res_72_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___boxed(lean_object* v_00_u03b2_73_, lean_object* v_m_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(v_00_u03b2_73_, v_m_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_m_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(lean_object* v_00_u03b2_78_, lean_object* v_a_79_, lean_object* v_x_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_79_, v_x_80_);
return v___x_81_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_79_ = stack[1].m_obj;
lean_object* v_x_80_ = stack[2].m_obj;
uint8_t v_res_82_;
v_res_82_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(lean_box(0), v_a_79_, v_x_80_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_83_, lean_object* v_a_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(v_00_u03b2_83_, v_a_84_, v_x_85_);
lean_dec(v_x_85_);
lean_dec(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(lean_object* v___x_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_88_);
lean_ctor_set(v___x_91_, 1, v___y_90_);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0___boxed(lean_object* v___x_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(v___x_93_, v___y_94_, v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_96_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(lean_object* v_f_97_, lean_object* v_as_98_, size_t v_i_99_, size_t v_stop_100_, lean_object* v_b_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_usize_dec_eq(v_i_99_, v_stop_100_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_array_uget_borrowed(v_as_98_, v_i_99_);
lean_inc_ref(v_f_97_);
lean_inc_ref(v___y_102_);
lean_inc(v___x_105_);
v___x_106_ = lean_apply_3(v_f_97_, v___x_105_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_dec_ref(v_f_97_);
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v_fst_108_; lean_object* v_snd_109_; size_t v___x_110_; size_t v___x_111_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v_fst_108_ = lean_ctor_get(v_a_107_, 0);
lean_inc(v_fst_108_);
v_snd_109_ = lean_ctor_get(v_a_107_, 1);
lean_inc(v_snd_109_);
lean_dec(v_a_107_);
v___x_110_ = ((size_t)1ULL);
v___x_111_ = lean_usize_add(v_i_99_, v___x_110_);
v_i_99_ = v___x_111_;
v_b_101_ = v_fst_108_;
v___y_103_ = v_snd_109_;
goto _start;
}
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec_ref(v_f_97_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_b_101_);
lean_ctor_set(v___x_113_, 1, v___y_103_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_97_ = stack[0].m_obj;
lean_object* v_as_98_ = stack[1].m_obj;
size_t v_i_99_ = stack[2].m_num;
size_t v_stop_100_ = stack[3].m_num;
lean_object* v_b_101_ = stack[4].m_obj;
lean_object* v___y_102_ = stack[5].m_obj;
lean_object* v___y_103_ = stack[6].m_obj;
lean_object* v_res_115_;
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_97_, v_as_98_, v_i_99_, v_stop_100_, v_b_101_, v___y_102_, v___y_103_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed(lean_object* v_f_116_, lean_object* v_as_117_, lean_object* v_i_118_, lean_object* v_stop_119_, lean_object* v_b_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
size_t v_i_boxed_123_; size_t v_stop_boxed_124_; lean_object* v_res_125_; 
v_i_boxed_123_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_stop_boxed_124_ = lean_unbox_usize(v_stop_119_);
lean_dec(v_stop_119_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_116_, v_as_117_, v_i_boxed_123_, v_stop_boxed_124_, v_b_120_, v___y_121_, v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec_ref(v_as_117_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(lean_object* v_f_126_, lean_object* v_as_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
if (lean_obj_tag(v_as_127_) == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec_ref(v_f_126_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___y_129_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
else
{
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v___x_135_; 
v_head_133_ = lean_ctor_get(v_as_127_, 0);
lean_inc(v_head_133_);
v_tail_134_ = lean_ctor_get(v_as_127_, 1);
lean_inc(v_tail_134_);
lean_dec_ref_known(v_as_127_, 2);
lean_inc_ref(v_f_126_);
lean_inc_ref(v___y_128_);
v___x_135_ = lean_apply_3(v_f_126_, v_head_133_, v___y_128_, v___y_129_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_dec(v_tail_134_);
lean_dec_ref(v_f_126_);
return v___x_135_;
}
else
{
lean_object* v_a_136_; lean_object* v_snd_137_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v_snd_137_ = lean_ctor_get(v_a_136_, 1);
lean_inc(v_snd_137_);
lean_dec(v_a_136_);
v_as_127_ = v_tail_134_;
v___y_129_ = v_snd_137_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1___boxed(lean_object* v_f_139_, lean_object* v_as_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_139_, v_as_140_, v___y_141_, v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(lean_object* v_f_144_, lean_object* v_as_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
if (lean_obj_tag(v_as_145_) == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_f_144_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___y_147_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v_ctor_153_; lean_object* v_rhs_154_; lean_object* v___x_155_; 
v_head_151_ = lean_ctor_get(v_as_145_, 0);
lean_inc(v_head_151_);
v_tail_152_ = lean_ctor_get(v_as_145_, 1);
lean_inc(v_tail_152_);
lean_dec_ref_known(v_as_145_, 2);
v_ctor_153_ = lean_ctor_get(v_head_151_, 0);
lean_inc(v_ctor_153_);
v_rhs_154_ = lean_ctor_get(v_head_151_, 2);
lean_inc_ref(v_rhs_154_);
lean_dec(v_head_151_);
lean_inc_ref(v_f_144_);
lean_inc_ref(v___y_146_);
v___x_155_ = lean_apply_3(v_f_144_, v_ctor_153_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_dec_ref(v_rhs_154_);
lean_dec(v_tail_152_);
lean_dec_ref(v_f_144_);
return v___x_155_;
}
else
{
lean_object* v_a_156_; lean_object* v_snd_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
v_snd_157_ = lean_ctor_get(v_a_156_, 1);
lean_inc(v_snd_157_);
lean_dec(v_a_156_);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = l_Lean_Expr_getUsedConstants(v_rhs_154_);
v___x_160_ = lean_array_get_size(v___x_159_);
v___x_161_ = lean_nat_dec_lt(v___x_158_, v___x_160_);
if (v___x_161_ == 0)
{
lean_dec_ref(v___x_159_);
v_as_145_ = v_tail_152_;
v___y_147_ = v_snd_157_;
goto _start;
}
else
{
lean_object* v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_box(0);
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_160_);
lean_inc_ref(v_f_144_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_144_, v___x_159_, v___x_164_, v___x_165_, v___x_163_, v___y_146_, v_snd_157_);
lean_dec_ref(v___x_159_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_dec(v_tail_152_);
lean_dec_ref(v_f_144_);
return v___x_166_;
}
else
{
lean_object* v_a_167_; lean_object* v_snd_168_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v_snd_168_ = lean_ctor_get(v_a_167_, 1);
lean_inc(v_snd_168_);
lean_dec(v_a_167_);
v_as_145_ = v_tail_152_;
v___y_147_ = v_snd_168_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2___boxed(lean_object* v_f_170_, lean_object* v_as_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(v_f_170_, v_as_171_, v___y_172_, v___y_173_);
lean_dec_ref(v___y_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(lean_object* v_info_179_, lean_object* v_f_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___y_206_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_202_ = l_Lean_ConstantInfo_type(v_info_179_);
v___x_203_ = l_Lean_Expr_getUsedConstants(v___x_202_);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_array_get_size(v___x_203_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_nat_dec_lt(v___x_204_, v___x_226_);
if (v___x_228_ == 0)
{
lean_object* v___f_229_; 
lean_dec_ref(v___x_203_);
v___f_229_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___closed__0));
v___y_206_ = v___f_229_;
goto v___jp_205_;
}
else
{
size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_230_ = lean_usize_of_nat(v___x_226_);
v___x_231_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed__const__1));
v___x_232_ = lean_box_usize(v___x_230_);
lean_inc_ref(v_f_180_);
v___x_233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed), 7, 5);
lean_closure_set(v___x_233_, 0, v_f_180_);
lean_closure_set(v___x_233_, 1, v___x_203_);
lean_closure_set(v___x_233_, 2, v___x_231_);
lean_closure_set(v___x_233_, 3, v___x_232_);
lean_closure_set(v___x_233_, 4, v___x_227_);
v___y_206_ = v___x_233_;
goto v___jp_205_;
}
v___jp_183_:
{
switch(lean_obj_tag(v_info_179_))
{
case 5:
{
lean_object* v_val_186_; lean_object* v_all_187_; lean_object* v_ctors_188_; lean_object* v___x_189_; 
v_val_186_ = lean_ctor_get(v_info_179_, 0);
lean_inc_ref(v_val_186_);
lean_dec_ref_known(v_info_179_, 1);
v_all_187_ = lean_ctor_get(v_val_186_, 3);
lean_inc(v_all_187_);
v_ctors_188_ = lean_ctor_get(v_val_186_, 4);
lean_inc(v_ctors_188_);
lean_dec_ref(v_val_186_);
lean_inc_ref(v_f_180_);
v___x_189_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_180_, v_ctors_188_, v___y_184_, v___y_185_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_dec(v_all_187_);
lean_dec_ref(v_f_180_);
return v___x_189_;
}
else
{
lean_object* v_a_190_; lean_object* v_snd_191_; lean_object* v___x_192_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
v_snd_191_ = lean_ctor_get(v_a_190_, 1);
lean_inc(v_snd_191_);
lean_dec(v_a_190_);
v___x_192_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_180_, v_all_187_, v___y_184_, v_snd_191_);
return v___x_192_;
}
}
case 6:
{
lean_object* v_val_193_; lean_object* v_induct_194_; lean_object* v___x_195_; 
v_val_193_ = lean_ctor_get(v_info_179_, 0);
lean_inc_ref(v_val_193_);
lean_dec_ref_known(v_info_179_, 1);
v_induct_194_ = lean_ctor_get(v_val_193_, 1);
lean_inc(v_induct_194_);
lean_dec_ref(v_val_193_);
lean_inc_ref(v___y_184_);
v___x_195_ = lean_apply_3(v_f_180_, v_induct_194_, v___y_184_, v___y_185_);
return v___x_195_;
}
case 7:
{
lean_object* v_val_196_; lean_object* v_rules_197_; lean_object* v___x_198_; 
v_val_196_ = lean_ctor_get(v_info_179_, 0);
lean_inc_ref(v_val_196_);
lean_dec_ref_known(v_info_179_, 1);
v_rules_197_ = lean_ctor_get(v_val_196_, 6);
lean_inc(v_rules_197_);
lean_dec_ref(v_val_196_);
v___x_198_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(v_f_180_, v_rules_197_, v___y_184_, v___y_185_);
return v___x_198_;
}
default: 
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_dec_ref(v_f_180_);
lean_dec_ref(v_info_179_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___y_185_);
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
v___jp_205_:
{
lean_object* v___x_207_; 
lean_inc_ref(v___y_181_);
v___x_207_ = lean_apply_2(v___y_206_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_dec_ref(v_f_180_);
lean_dec_ref(v_info_179_);
return v___x_207_;
}
else
{
lean_object* v_a_208_; lean_object* v_snd_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v_snd_209_ = lean_ctor_get(v_a_208_, 1);
lean_inc(v_snd_209_);
lean_dec(v_a_208_);
v___x_210_ = l_Lean_ConstantInfo_name(v_info_179_);
lean_inc_ref(v_f_180_);
lean_inc_ref(v___y_181_);
v___x_211_ = lean_apply_3(v_f_180_, v___x_210_, v___y_181_, v_snd_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_dec_ref(v_f_180_);
lean_dec_ref(v_info_179_);
return v___x_211_;
}
else
{
lean_object* v_a_212_; lean_object* v_snd_213_; uint8_t v___x_214_; lean_object* v___x_215_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v_snd_213_ = lean_ctor_get(v_a_212_, 1);
lean_inc(v_snd_213_);
lean_dec(v_a_212_);
v___x_214_ = 1;
lean_inc_ref(v_info_179_);
v___x_215_ = l_Lean_ConstantInfo_value_x3f(v_info_179_, v___x_214_);
if (lean_obj_tag(v___x_215_) == 1)
{
lean_object* v_val_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_val_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_215_, 1);
v___x_217_ = l_Lean_Expr_getUsedConstants(v_val_216_);
v___x_218_ = lean_array_get_size(v___x_217_);
v___x_219_ = lean_nat_dec_lt(v___x_204_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v___x_217_);
v___y_184_ = v___y_181_;
v___y_185_ = v_snd_213_;
goto v___jp_183_;
}
else
{
lean_object* v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_box(0);
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_218_);
lean_inc_ref(v_f_180_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_180_, v___x_217_, v___x_221_, v___x_222_, v___x_220_, v___y_181_, v_snd_213_);
lean_dec_ref(v___x_217_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_dec_ref(v_f_180_);
lean_dec_ref(v_info_179_);
return v___x_223_;
}
else
{
lean_object* v_a_224_; lean_object* v_snd_225_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v_snd_225_ = lean_ctor_get(v_a_224_, 1);
lean_inc(v_snd_225_);
lean_dec(v_a_224_);
v___y_184_ = v___y_181_;
v___y_185_ = v_snd_225_;
goto v___jp_183_;
}
}
}
else
{
lean_dec(v___x_215_);
v___y_184_ = v___y_181_;
v___y_185_ = v_snd_213_;
goto v___jp_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed(lean_object* v_info_234_, lean_object* v_f_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(v_info_234_, v_f_235_, v___y_236_, v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(lean_object* v_info_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___closed__0));
v___x_244_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(v_info_240_, v___x_243_, v_a_241_, v_a_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___boxed(lean_object* v_info_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_info_245_, v_a_246_, v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(lean_object* v_a_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
else
{
lean_object* v_key_252_; lean_object* v_value_253_; lean_object* v_tail_254_; uint8_t v___x_255_; 
v_key_252_ = lean_ctor_get(v_x_250_, 0);
v_value_253_ = lean_ctor_get(v_x_250_, 1);
v_tail_254_ = lean_ctor_get(v_x_250_, 2);
v___x_255_ = lean_name_eq(v_key_252_, v_a_249_);
if (v___x_255_ == 0)
{
v_x_250_ = v_tail_254_;
goto _start;
}
else
{
lean_object* v___x_257_; 
lean_inc(v_value_253_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v_value_253_);
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg___boxed(lean_object* v_a_258_, lean_object* v_x_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_258_, v_x_259_);
lean_dec(v_x_259_);
lean_dec(v_a_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(lean_object* v_m_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_buckets_263_; lean_object* v___x_264_; uint64_t v___y_266_; 
v_buckets_263_ = lean_ctor_get(v_m_261_, 1);
v___x_264_ = lean_array_get_size(v_buckets_263_);
if (lean_obj_tag(v_a_262_) == 0)
{
uint64_t v___x_280_; 
v___x_280_ = 1723ULL;
v___y_266_ = v___x_280_;
goto v___jp_265_;
}
else
{
uint64_t v_hash_281_; 
v_hash_281_ = lean_ctor_get_uint64(v_a_262_, sizeof(void*)*2);
v___y_266_ = v_hash_281_;
goto v___jp_265_;
}
v___jp_265_:
{
uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v_fold_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_267_ = 32ULL;
v___x_268_ = lean_uint64_shift_right(v___y_266_, v___x_267_);
v_fold_269_ = lean_uint64_xor(v___y_266_, v___x_268_);
v___x_270_ = 16ULL;
v___x_271_ = lean_uint64_shift_right(v_fold_269_, v___x_270_);
v___x_272_ = lean_uint64_xor(v_fold_269_, v___x_271_);
v___x_273_ = lean_uint64_to_usize(v___x_272_);
v___x_274_ = lean_usize_of_nat(v___x_264_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_sub(v___x_274_, v___x_275_);
v___x_277_ = lean_usize_land(v___x_273_, v___x_276_);
v___x_278_ = lean_array_uget_borrowed(v_buckets_263_, v___x_277_);
v___x_279_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_262_, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg___boxed(lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_m_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
return v_x_285_;
}
else
{
lean_object* v_key_287_; lean_object* v_value_288_; lean_object* v_tail_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_315_; 
v_key_287_ = lean_ctor_get(v_x_286_, 0);
v_value_288_ = lean_ctor_get(v_x_286_, 1);
v_tail_289_ = lean_ctor_get(v_x_286_, 2);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_315_ == 0)
{
v___x_291_ = v_x_286_;
v_isShared_292_ = v_isSharedCheck_315_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_tail_289_);
lean_inc(v_value_288_);
lean_inc(v_key_287_);
lean_dec(v_x_286_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_315_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; uint64_t v___y_295_; 
v___x_293_ = lean_array_get_size(v_x_285_);
if (lean_obj_tag(v_key_287_) == 0)
{
uint64_t v___x_313_; 
v___x_313_ = 1723ULL;
v___y_295_ = v___x_313_;
goto v___jp_294_;
}
else
{
uint64_t v_hash_314_; 
v_hash_314_ = lean_ctor_get_uint64(v_key_287_, sizeof(void*)*2);
v___y_295_ = v_hash_314_;
goto v___jp_294_;
}
v___jp_294_:
{
uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v_fold_298_; uint64_t v___x_299_; uint64_t v___x_300_; uint64_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_296_ = 32ULL;
v___x_297_ = lean_uint64_shift_right(v___y_295_, v___x_296_);
v_fold_298_ = lean_uint64_xor(v___y_295_, v___x_297_);
v___x_299_ = 16ULL;
v___x_300_ = lean_uint64_shift_right(v_fold_298_, v___x_299_);
v___x_301_ = lean_uint64_xor(v_fold_298_, v___x_300_);
v___x_302_ = lean_uint64_to_usize(v___x_301_);
v___x_303_ = lean_usize_of_nat(v___x_293_);
v___x_304_ = ((size_t)1ULL);
v___x_305_ = lean_usize_sub(v___x_303_, v___x_304_);
v___x_306_ = lean_usize_land(v___x_302_, v___x_305_);
v___x_307_ = lean_array_uget_borrowed(v_x_285_, v___x_306_);
lean_inc(v___x_307_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 2, v___x_307_);
v___x_309_ = v___x_291_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_key_287_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_value_288_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v___x_307_);
v___x_309_ = v_reuseFailAlloc_312_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; 
v___x_310_ = lean_array_uset(v_x_285_, v___x_306_, v___x_309_);
v_x_285_ = v___x_310_;
v_x_286_ = v_tail_289_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(lean_object* v_i_316_, lean_object* v_source_317_, lean_object* v_target_318_){
_start:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_array_get_size(v_source_317_);
v___x_320_ = lean_nat_dec_lt(v_i_316_, v___x_319_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_source_317_);
lean_dec(v_i_316_);
return v_target_318_;
}
else
{
lean_object* v_es_321_; lean_object* v___x_322_; lean_object* v_source_323_; lean_object* v_target_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_es_321_ = lean_array_fget(v_source_317_, v_i_316_);
v___x_322_ = lean_box(0);
v_source_323_ = lean_array_fset(v_source_317_, v_i_316_, v___x_322_);
v_target_324_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_target_318_, v_es_321_);
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_i_316_, v___x_325_);
lean_dec(v_i_316_);
v_i_316_ = v___x_326_;
v_source_317_ = v_source_323_;
v_target_318_ = v_target_324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(lean_object* v_data_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_nbuckets_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_329_ = lean_array_get_size(v_data_328_);
v___x_330_ = lean_unsigned_to_nat(2u);
v_nbuckets_331_ = lean_nat_mul(v___x_329_, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_box(0);
v___x_334_ = lean_mk_array(v_nbuckets_331_, v___x_333_);
v___x_335_ = lean_array_propagate_mark(v_data_328_, v___x_334_);
v___x_336_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v___x_332_, v_data_328_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(lean_object* v_m_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
lean_object* v_size_340_; lean_object* v_buckets_341_; lean_object* v___x_342_; uint64_t v___y_344_; 
v_size_340_ = lean_ctor_get(v_m_337_, 0);
v_buckets_341_ = lean_ctor_get(v_m_337_, 1);
v___x_342_ = lean_array_get_size(v_buckets_341_);
if (lean_obj_tag(v_a_338_) == 0)
{
uint64_t v___x_381_; 
v___x_381_ = 1723ULL;
v___y_344_ = v___x_381_;
goto v___jp_343_;
}
else
{
uint64_t v_hash_382_; 
v_hash_382_ = lean_ctor_get_uint64(v_a_338_, sizeof(void*)*2);
v___y_344_ = v_hash_382_;
goto v___jp_343_;
}
v___jp_343_:
{
uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v_fold_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v_bkt_356_; uint8_t v___x_357_; 
v___x_345_ = 32ULL;
v___x_346_ = lean_uint64_shift_right(v___y_344_, v___x_345_);
v_fold_347_ = lean_uint64_xor(v___y_344_, v___x_346_);
v___x_348_ = 16ULL;
v___x_349_ = lean_uint64_shift_right(v_fold_347_, v___x_348_);
v___x_350_ = lean_uint64_xor(v_fold_347_, v___x_349_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = lean_usize_of_nat(v___x_342_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_sub(v___x_352_, v___x_353_);
v___x_355_ = lean_usize_land(v___x_351_, v___x_354_);
v_bkt_356_ = lean_array_uget_borrowed(v_buckets_341_, v___x_355_);
v___x_357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_338_, v_bkt_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_378_; 
lean_inc_ref(v_buckets_341_);
lean_inc(v_size_340_);
v_isSharedCheck_378_ = !lean_is_exclusive(v_m_337_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; lean_object* v_unused_380_; 
v_unused_379_ = lean_ctor_get(v_m_337_, 1);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_m_337_, 0);
lean_dec(v_unused_380_);
v___x_359_ = v_m_337_;
v_isShared_360_ = v_isSharedCheck_378_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_m_337_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_378_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v_size_x27_362_; lean_object* v___x_363_; lean_object* v_buckets_x27_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v_size_x27_362_ = lean_nat_add(v_size_340_, v___x_361_);
lean_dec(v_size_340_);
lean_inc(v_bkt_356_);
v___x_363_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_363_, 0, v_a_338_);
lean_ctor_set(v___x_363_, 1, v_b_339_);
lean_ctor_set(v___x_363_, 2, v_bkt_356_);
v_buckets_x27_364_ = lean_array_uset(v_buckets_341_, v___x_355_, v___x_363_);
v___x_365_ = lean_unsigned_to_nat(4u);
v___x_366_ = lean_nat_mul(v_size_x27_362_, v___x_365_);
v___x_367_ = lean_unsigned_to_nat(3u);
v___x_368_ = lean_nat_div(v___x_366_, v___x_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_array_get_size(v_buckets_x27_364_);
v___x_370_ = lean_nat_dec_le(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
if (v___x_370_ == 0)
{
lean_object* v_val_371_; lean_object* v___x_373_; 
v_val_371_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_buckets_x27_364_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_val_371_);
lean_ctor_set(v___x_359_, 0, v_size_x27_362_);
v___x_373_ = v___x_359_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_size_x27_362_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_val_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
else
{
lean_object* v___x_376_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_buckets_x27_364_);
lean_ctor_set(v___x_359_, 0, v_size_x27_362_);
v___x_376_ = v___x_359_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_size_x27_362_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_buckets_x27_364_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_dec(v_b_339_);
lean_dec(v_a_338_);
return v_m_337_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(lean_object* v_as_383_, size_t v_i_384_, size_t v_stop_385_, lean_object* v_b_386_, lean_object* v___y_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_eq(v_i_384_, v_stop_385_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_array_uget_borrowed(v_as_383_, v_i_384_);
lean_inc(v___x_389_);
v___x_390_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(v___x_389_, v___y_387_);
if (lean_obj_tag(v___x_390_) == 0)
{
return v___x_390_;
}
else
{
lean_object* v_a_391_; lean_object* v_fst_392_; lean_object* v_snd_393_; size_t v___x_394_; size_t v___x_395_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v_fst_392_ = lean_ctor_get(v_a_391_, 0);
lean_inc(v_fst_392_);
v_snd_393_ = lean_ctor_get(v_a_391_, 1);
lean_inc(v_snd_393_);
lean_dec(v_a_391_);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_add(v_i_384_, v___x_394_);
v_i_384_ = v___x_395_;
v_b_386_ = v_fst_392_;
v___y_387_ = v_snd_393_;
goto _start;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_b_386_);
lean_ctor_set(v___x_397_, 1, v___y_387_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_383_ = stack[0].m_obj;
size_t v_i_384_ = stack[1].m_num;
size_t v_stop_385_ = stack[2].m_num;
lean_object* v_b_386_ = stack[3].m_obj;
lean_object* v___y_387_ = stack[4].m_obj;
lean_object* v_res_399_;
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_383_, v_i_384_, v_stop_385_, v_b_386_, v___y_387_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg___boxed(lean_object* v_as_400_, lean_object* v_i_401_, lean_object* v_stop_402_, lean_object* v_b_403_, lean_object* v___y_404_){
_start:
{
size_t v_i_boxed_405_; size_t v_stop_boxed_406_; lean_object* v_res_407_; 
v_i_boxed_405_ = lean_unbox_usize(v_i_401_);
lean_dec(v_i_401_);
v_stop_boxed_406_ = lean_unbox_usize(v_stop_402_);
lean_dec(v_stop_402_);
v_res_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_400_, v_i_boxed_405_, v_stop_boxed_406_, v_b_403_, v___y_404_);
lean_dec_ref(v_as_400_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_worklist_414_; lean_object* v_checked_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v_worklist_414_ = lean_ctor_get(v_a_413_, 0);
v_checked_415_ = lean_ctor_get(v_a_413_, 1);
v___x_416_ = lean_array_get_size(v_worklist_414_);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_nat_dec_eq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_512_; 
lean_inc_ref(v_checked_415_);
lean_inc_ref(v_worklist_414_);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_413_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; lean_object* v_unused_514_; 
v_unused_513_ = lean_ctor_get(v_a_413_, 1);
lean_dec(v_unused_513_);
v_unused_514_ = lean_ctor_get(v_a_413_, 0);
lean_dec(v_unused_514_);
v___x_420_ = v_a_413_;
v_isShared_421_ = v_isSharedCheck_512_;
goto v_resetjp_419_;
}
else
{
lean_dec(v_a_413_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_512_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___y_427_; lean_object* v_worklist_428_; lean_object* v_checked_429_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_442_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_422_ = lean_box(0);
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = lean_nat_sub(v___x_416_, v___x_423_);
v___x_425_ = lean_array_get(v___x_422_, v_worklist_414_, v___x_424_);
lean_dec(v___x_424_);
v___x_445_ = lean_array_pop(v_worklist_414_);
lean_inc_ref(v_checked_415_);
lean_inc_ref(v___x_445_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_checked_415_);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_415_, v___x_425_);
if (v___x_447_ == 0)
{
lean_object* v_challenge_448_; lean_object* v_solution_449_; lean_object* v_definitionTargets_450_; lean_object* v_theoremTargets_451_; lean_object* v_constMap_452_; lean_object* v___x_453_; 
v_challenge_448_ = lean_ctor_get(v_a_412_, 0);
v_solution_449_ = lean_ctor_get(v_a_412_, 1);
v_definitionTargets_450_ = lean_ctor_get(v_a_412_, 2);
v_theoremTargets_451_ = lean_ctor_get(v_a_412_, 3);
v_constMap_452_ = lean_ctor_get(v_challenge_448_, 0);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_452_, v___x_425_);
if (lean_obj_tag(v___x_453_) == 1)
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_503_; 
v_val_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_503_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_503_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_503_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_constMap_458_; lean_object* v___x_459_; 
v_constMap_458_ = lean_ctor_get(v_solution_449_, 0);
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_458_, v___x_425_);
if (lean_obj_tag(v___x_459_) == 1)
{
lean_object* v_val_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_493_; 
lean_del_object(v___x_456_);
v_val_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_493_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_493_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_val_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_493_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = l_Lean_ConstantInfo_name(v_val_460_);
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_definitionTargets_450_, v___x_477_);
if (v___x_478_ == 0)
{
uint8_t v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_theoremTargets_451_, v___x_477_);
lean_dec(v___x_477_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
lean_dec_ref(v___x_445_);
lean_dec_ref(v_checked_415_);
v___x_480_ = l_Lean_instBEqConstantInfo_beq(v_val_454_, v_val_460_);
lean_dec(v_val_454_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
lean_dec(v_val_460_);
lean_dec_ref_known(v___x_446_, 2);
lean_del_object(v___x_420_);
v___x_481_ = 1;
v___x_482_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
v___x_483_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_425_, v___x_481_);
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
if (v_isShared_463_ == 0)
{
lean_ctor_set_tag(v___x_462_, 0);
lean_ctor_set(v___x_462_, 0, v___x_486_);
v___x_488_ = v___x_462_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_object* v___x_490_; 
lean_del_object(v___x_462_);
v___x_490_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_val_460_, v_a_412_, v___x_446_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec(v___x_425_);
lean_del_object(v___x_420_);
return v___x_490_;
}
else
{
lean_object* v_a_491_; lean_object* v_snd_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v_snd_492_ = lean_ctor_get(v_a_491_, 1);
lean_inc(v_snd_492_);
lean_dec(v_a_491_);
v___y_437_ = v_a_412_;
v___y_438_ = v_snd_492_;
goto v___jp_436_;
}
}
}
else
{
lean_del_object(v___x_462_);
lean_dec(v_val_454_);
goto v___jp_464_;
}
}
else
{
lean_dec(v___x_477_);
lean_del_object(v___x_462_);
lean_dec(v_val_454_);
goto v___jp_464_;
}
v___jp_464_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_465_ = l_Lean_ConstantInfo_type(v_val_460_);
lean_dec(v_val_460_);
v___x_466_ = l_Lean_Expr_getUsedConstants(v___x_465_);
v___x_467_ = lean_array_get_size(v___x_466_);
v___x_468_ = lean_nat_dec_lt(v___x_417_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec_ref(v___x_466_);
lean_dec_ref_known(v___x_446_, 2);
v___y_427_ = v_a_412_;
v_worklist_428_ = v___x_445_;
v_checked_429_ = v_checked_415_;
goto v___jp_426_;
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_box(0);
v___x_470_ = lean_nat_dec_le(v___x_467_, v___x_467_);
if (v___x_470_ == 0)
{
if (v___x_468_ == 0)
{
lean_dec_ref(v___x_466_);
lean_dec_ref_known(v___x_446_, 2);
v___y_427_ = v_a_412_;
v_worklist_428_ = v___x_445_;
v_checked_429_ = v_checked_415_;
goto v___jp_426_;
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
lean_dec_ref(v___x_445_);
lean_dec_ref(v_checked_415_);
v___x_471_ = ((size_t)0ULL);
v___x_472_ = lean_usize_of_nat(v___x_467_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_466_, v___x_471_, v___x_472_, v___x_469_, v___x_446_);
lean_dec_ref(v___x_466_);
v___y_442_ = v___x_473_;
goto v___jp_441_;
}
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v___x_445_);
lean_dec_ref(v_checked_415_);
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_467_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_466_, v___x_474_, v___x_475_, v___x_469_, v___x_446_);
lean_dec_ref(v___x_466_);
v___y_442_ = v___x_476_;
goto v___jp_441_;
}
}
}
}
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
lean_dec(v___x_459_);
lean_dec(v_val_454_);
lean_dec_ref_known(v___x_446_, 2);
lean_dec_ref(v___x_445_);
lean_del_object(v___x_420_);
lean_dec_ref(v_checked_415_);
v___x_494_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2));
v___x_495_ = 1;
v___x_496_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_425_, v___x_495_);
v___x_497_ = lean_string_append(v___x_494_, v___x_496_);
lean_dec_ref(v___x_496_);
v___x_498_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 0);
lean_ctor_set(v___x_456_, 0, v___x_499_);
v___x_501_ = v___x_456_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v___x_453_);
lean_dec_ref_known(v___x_446_, 2);
lean_dec_ref(v___x_445_);
lean_del_object(v___x_420_);
lean_dec_ref(v_checked_415_);
v___x_504_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3));
v___x_505_ = 1;
v___x_506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_425_, v___x_505_);
v___x_507_ = lean_string_append(v___x_504_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
else
{
lean_dec_ref(v___x_445_);
lean_dec(v___x_425_);
lean_del_object(v___x_420_);
lean_dec_ref(v_checked_415_);
v_a_413_ = v___x_446_;
goto _start;
}
v___jp_426_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_box(0);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_checked_429_, v___x_425_, v___x_430_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_431_);
lean_ctor_set(v___x_420_, 0, v_worklist_428_);
v___x_433_ = v___x_420_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_worklist_428_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_431_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
v_a_412_ = v___y_427_;
v_a_413_ = v___x_433_;
goto _start;
}
}
v___jp_436_:
{
lean_object* v_worklist_439_; lean_object* v_checked_440_; 
v_worklist_439_ = lean_ctor_get(v___y_438_, 0);
lean_inc_ref(v_worklist_439_);
v_checked_440_ = lean_ctor_get(v___y_438_, 1);
lean_inc_ref(v_checked_440_);
lean_dec_ref(v___y_438_);
v___y_427_ = v___y_437_;
v_worklist_428_ = v_worklist_439_;
v_checked_429_ = v_checked_440_;
goto v___jp_426_;
}
v___jp_441_:
{
if (lean_obj_tag(v___y_442_) == 0)
{
lean_dec(v___x_425_);
lean_del_object(v___x_420_);
return v___y_442_;
}
else
{
lean_object* v_a_443_; lean_object* v_snd_444_; 
v_a_443_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___y_442_, 1);
v_snd_444_ = lean_ctor_get(v_a_443_, 1);
lean_inc(v_snd_444_);
lean_dec(v_a_443_);
v___y_437_ = v_a_412_;
v___y_438_ = v_snd_444_;
goto v___jp_436_;
}
}
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v_a_413_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___boxed(lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v_a_518_, v_a_519_);
lean_dec_ref(v_a_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0(lean_object* v_00_u03b2_521_, lean_object* v_m_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_m_522_, v_a_523_, v_b_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(lean_object* v_00_u03b2_526_, lean_object* v_m_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_527_, v_a_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___boxed(lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(v_00_u03b2_530_, v_m_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_m_531_);
return v_res_533_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(lean_object* v_as_534_, size_t v_i_535_, size_t v_stop_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_534_, v_i_535_, v_stop_536_, v_b_537_, v___y_539_);
return v___x_540_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_534_ = stack[0].m_obj;
size_t v_i_535_ = stack[1].m_num;
size_t v_stop_536_ = stack[2].m_num;
lean_object* v_b_537_ = stack[3].m_obj;
lean_object* v___y_538_ = stack[4].m_obj;
lean_object* v___y_539_ = stack[5].m_obj;
lean_object* v_res_541_;
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(v_as_534_, v_i_535_, v_stop_536_, v_b_537_, v___y_538_, v___y_539_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___boxed(lean_object* v_as_542_, lean_object* v_i_543_, lean_object* v_stop_544_, lean_object* v_b_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
size_t v_i_boxed_548_; size_t v_stop_boxed_549_; lean_object* v_res_550_; 
v_i_boxed_548_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_stop_boxed_549_ = lean_unbox_usize(v_stop_544_);
lean_dec(v_stop_544_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(v_as_542_, v_i_boxed_548_, v_stop_boxed_549_, v_b_545_, v___y_546_, v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v_as_542_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0(lean_object* v_00_u03b2_551_, lean_object* v_data_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_data_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(lean_object* v_00_u03b2_554_, lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___boxed(lean_object* v_00_u03b2_558_, lean_object* v_a_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(v_00_u03b2_558_, v_a_559_, v_x_560_);
lean_dec(v_x_560_);
lean_dec(v_a_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_562_, lean_object* v_i_563_, lean_object* v_source_564_, lean_object* v_target_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v_i_563_, v_source_564_, v_target_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_x_568_, v_x_569_);
return v___x_570_;
}
}
uint8_t l_Lake_Check_definitionHoleMatches(lean_object* v_challengeHole_571_, lean_object* v_solutionHole_572_){
_start:
{
lean_object* v_toConstantVal_573_; uint8_t v_safety_574_; lean_object* v_toConstantVal_575_; uint8_t v_safety_576_; uint8_t v___x_577_; 
v_toConstantVal_573_ = lean_ctor_get(v_challengeHole_571_, 0);
v_safety_574_ = lean_ctor_get_uint8(v_challengeHole_571_, sizeof(void*)*4);
v_toConstantVal_575_ = lean_ctor_get(v_solutionHole_572_, 0);
v_safety_576_ = lean_ctor_get_uint8(v_solutionHole_572_, sizeof(void*)*4);
v___x_577_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_573_, v_toConstantVal_575_);
if (v___x_577_ == 0)
{
return v___x_577_;
}
else
{
uint8_t v___x_578_; 
v___x_578_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_574_, v_safety_576_);
return v___x_578_;
}
}
}
LEAN_EXPORT void l_Lake_Check_definitionHoleMatches_0interp(lean_interpreter_value* stack)
{
lean_object* v_challengeHole_571_ = stack[0].m_obj;
lean_object* v_solutionHole_572_ = stack[1].m_obj;
uint8_t v_res_579_;
v_res_579_ = l_Lake_Check_definitionHoleMatches(v_challengeHole_571_, v_solutionHole_572_);
stack->m_num = v_res_579_;
}
LEAN_EXPORT lean_object* l_Lake_Check_definitionHoleMatches___boxed(lean_object* v_challengeHole_580_, lean_object* v_solutionHole_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Lake_Check_definitionHoleMatches(v_challengeHole_580_, v_solutionHole_581_);
lean_dec_ref(v_solutionHole_581_);
lean_dec_ref(v_challengeHole_580_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(lean_object* v_as_584_, size_t v_sz_585_, size_t v_i_586_, lean_object* v_b_587_){
_start:
{
uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_lt(v_i_586_, v_sz_585_);
if (v___x_588_ == 0)
{
return v_b_587_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v_r_591_; size_t v___x_592_; size_t v___x_593_; 
v_a_589_ = lean_array_uget_borrowed(v_as_584_, v_i_586_);
v___x_590_ = lean_box(0);
lean_inc(v_a_589_);
v_r_591_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_b_587_, v_a_589_, v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_586_, v___x_592_);
v_i_586_ = v___x_593_;
v_b_587_ = v_r_591_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_584_ = stack[0].m_obj;
size_t v_sz_585_ = stack[1].m_num;
size_t v_i_586_ = stack[2].m_num;
lean_object* v_b_587_ = stack[3].m_obj;
lean_object* v_res_595_;
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_as_584_, v_sz_585_, v_i_586_, v_b_587_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2___boxed(lean_object* v_as_596_, lean_object* v_sz_597_, lean_object* v_i_598_, lean_object* v_b_599_){
_start:
{
size_t v_sz_boxed_600_; size_t v_i_boxed_601_; lean_object* v_res_602_; 
v_sz_boxed_600_ = lean_unbox_usize(v_sz_597_);
lean_dec(v_sz_597_);
v_i_boxed_601_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_as_596_, v_sz_boxed_600_, v_i_boxed_601_, v_b_599_);
lean_dec_ref(v_as_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(lean_object* v_m_603_, lean_object* v_l_604_){
_start:
{
size_t v_sz_605_; size_t v___x_606_; lean_object* v___x_607_; 
v_sz_605_ = lean_array_size(v_l_604_);
v___x_606_ = ((size_t)0ULL);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_l_604_, v_sz_605_, v___x_606_, v_m_603_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2___boxed(lean_object* v_m_608_, lean_object* v_l_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v_m_608_, v_l_609_);
lean_dec_ref(v_l_609_);
return v_res_610_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(lean_object* v_challenge_615_, lean_object* v_solution_616_, lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_b_620_);
return v___x_622_;
}
else
{
lean_object* v_constMap_623_; lean_object* v_a_624_; lean_object* v___x_625_; 
v_constMap_623_ = lean_ctor_get(v_challenge_615_, 0);
v_a_624_ = lean_array_uget_borrowed(v_as_617_, v_i_619_);
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_623_, v_a_624_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_688_; 
v_val_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_688_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_688_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_val_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_688_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v_constMap_630_; lean_object* v___x_631_; 
v_constMap_630_ = lean_ctor_get(v_solution_616_, 0);
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_630_, v_a_624_);
if (lean_obj_tag(v___x_631_) == 1)
{
lean_del_object(v___x_628_);
if (lean_obj_tag(v_val_626_) == 1)
{
lean_object* v_val_632_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v___x_631_, 1);
if (lean_obj_tag(v_val_632_) == 1)
{
lean_object* v_val_633_; lean_object* v_val_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_653_; 
v_val_633_ = lean_ctor_get(v_val_626_, 0);
lean_inc_ref(v_val_633_);
lean_dec_ref_known(v_val_626_, 1);
v_val_634_ = lean_ctor_get(v_val_632_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_val_632_);
if (v_isSharedCheck_653_ == 0)
{
v___x_636_ = v_val_632_;
v_isShared_637_ = v_isSharedCheck_653_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_val_634_);
lean_dec(v_val_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_653_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
uint8_t v___x_638_; 
v___x_638_ = l_Lake_Check_definitionHoleMatches(v_val_633_, v_val_634_);
lean_dec_ref(v_val_633_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
lean_dec_ref(v_val_634_);
lean_dec_ref(v_b_620_);
v___x_639_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
lean_inc(v_a_624_);
v___x_640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_624_, v___x_621_);
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 0);
lean_ctor_set(v___x_636_, 0, v___x_643_);
v___x_645_ = v___x_636_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v_toConstantVal_647_; lean_object* v_name_648_; lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; 
lean_del_object(v___x_636_);
v_toConstantVal_647_ = lean_ctor_get(v_val_634_, 0);
lean_inc_ref(v_toConstantVal_647_);
lean_dec_ref(v_val_634_);
v_name_648_ = lean_ctor_get(v_toConstantVal_647_, 0);
lean_inc(v_name_648_);
lean_dec_ref(v_toConstantVal_647_);
v___x_649_ = lean_array_push(v_b_620_, v_name_648_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_619_, v___x_650_);
v_i_619_ = v___x_651_;
v_b_620_ = v___x_649_;
goto _start;
}
}
}
else
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_val_632_);
lean_dec_ref(v_b_620_);
v_isSharedCheck_665_ = !lean_is_exclusive(v_val_626_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_val_626_, 0);
lean_dec(v_unused_666_);
v___x_655_ = v_val_626_;
v_isShared_656_ = v_isSharedCheck_665_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_val_626_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_665_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0));
lean_inc(v_a_624_);
v___x_658_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_624_, v___x_621_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 0);
lean_ctor_set(v___x_655_, 0, v___x_661_);
v___x_663_ = v___x_655_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_val_626_);
lean_dec_ref(v_b_620_);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_631_, 0);
lean_dec(v_unused_679_);
v___x_668_ = v___x_631_;
v_isShared_669_ = v_isSharedCheck_678_;
goto v_resetjp_667_;
}
else
{
lean_dec(v___x_631_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_678_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1));
lean_inc(v_a_624_);
v___x_671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_624_, v___x_621_);
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 0);
lean_ctor_set(v___x_668_, 0, v___x_674_);
v___x_676_ = v___x_668_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec(v___x_631_);
lean_dec(v_val_626_);
lean_dec_ref(v_b_620_);
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_624_);
v___x_681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_624_, v___x_621_);
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
lean_dec_ref(v___x_681_);
v___x_683_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_684_ = lean_string_append(v___x_682_, v___x_683_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 0);
lean_ctor_set(v___x_628_, 0, v___x_684_);
v___x_686_ = v___x_628_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_625_);
lean_dec_ref(v_b_620_);
v___x_689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_624_);
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_624_, v___x_621_);
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
lean_dec_ref(v___x_690_);
v___x_692_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_challenge_615_ = stack[0].m_obj;
lean_object* v_solution_616_ = stack[1].m_obj;
lean_object* v_as_617_ = stack[2].m_obj;
size_t v_sz_618_ = stack[3].m_num;
size_t v_i_619_ = stack[4].m_num;
lean_object* v_b_620_ = stack[5].m_obj;
lean_object* v_res_695_;
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_615_, v_solution_616_, v_as_617_, v_sz_618_, v_i_619_, v_b_620_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___boxed(lean_object* v_challenge_696_, lean_object* v_solution_697_, lean_object* v_as_698_, lean_object* v_sz_699_, lean_object* v_i_700_, lean_object* v_b_701_){
_start:
{
size_t v_sz_boxed_702_; size_t v_i_boxed_703_; lean_object* v_res_704_; 
v_sz_boxed_702_ = lean_unbox_usize(v_sz_699_);
lean_dec(v_sz_699_);
v_i_boxed_703_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_696_, v_solution_697_, v_as_698_, v_sz_boxed_702_, v_i_boxed_703_, v_b_701_);
lean_dec_ref(v_as_698_);
lean_dec_ref(v_solution_697_);
lean_dec_ref(v_challenge_696_);
return v_res_704_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(lean_object* v_challenge_707_, lean_object* v_solution_708_, lean_object* v_as_709_, size_t v_sz_710_, size_t v_i_711_, lean_object* v_b_712_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = lean_usize_dec_lt(v_i_711_, v_sz_710_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_712_);
return v___x_714_;
}
else
{
lean_object* v_constMap_715_; lean_object* v_a_716_; lean_object* v_fst_725_; lean_object* v_snd_726_; lean_object* v___x_740_; 
v_constMap_715_ = lean_ctor_get(v_challenge_707_, 0);
v_a_716_ = lean_array_uget_borrowed(v_as_709_, v_i_711_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_715_, v_a_716_);
if (lean_obj_tag(v___x_740_) == 1)
{
lean_object* v_val_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_765_; 
v_val_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_765_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_val_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_constMap_745_; lean_object* v___x_746_; 
v_constMap_745_ = lean_ctor_get(v_solution_708_, 0);
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_745_, v_a_716_);
if (lean_obj_tag(v___x_746_) == 1)
{
lean_del_object(v___x_743_);
switch(lean_obj_tag(v_val_741_))
{
case 2:
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_746_, 1);
if (lean_obj_tag(v_val_747_) == 2)
{
lean_object* v_val_748_; lean_object* v_val_749_; lean_object* v_toConstantVal_750_; lean_object* v_toConstantVal_751_; 
v_val_748_ = lean_ctor_get(v_val_741_, 0);
lean_inc_ref(v_val_748_);
lean_dec_ref_known(v_val_741_, 1);
v_val_749_ = lean_ctor_get(v_val_747_, 0);
lean_inc_ref(v_val_749_);
lean_dec_ref_known(v_val_747_, 1);
v_toConstantVal_750_ = lean_ctor_get(v_val_748_, 0);
lean_inc_ref(v_toConstantVal_750_);
lean_dec_ref(v_val_748_);
v_toConstantVal_751_ = lean_ctor_get(v_val_749_, 0);
lean_inc_ref(v_toConstantVal_751_);
lean_dec_ref(v_val_749_);
v_fst_725_ = v_toConstantVal_750_;
v_snd_726_ = v_toConstantVal_751_;
goto v___jp_724_;
}
else
{
lean_dec(v_val_747_);
lean_dec_ref_known(v_val_741_, 1);
lean_dec_ref(v_b_712_);
goto v___jp_717_;
}
}
case 0:
{
lean_object* v_val_752_; 
v_val_752_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___x_746_, 1);
if (lean_obj_tag(v_val_752_) == 0)
{
lean_object* v_val_753_; lean_object* v_val_754_; lean_object* v_toConstantVal_755_; lean_object* v_toConstantVal_756_; 
v_val_753_ = lean_ctor_get(v_val_741_, 0);
lean_inc_ref(v_val_753_);
lean_dec_ref_known(v_val_741_, 1);
v_val_754_ = lean_ctor_get(v_val_752_, 0);
lean_inc_ref(v_val_754_);
lean_dec_ref_known(v_val_752_, 1);
v_toConstantVal_755_ = lean_ctor_get(v_val_753_, 0);
lean_inc_ref(v_toConstantVal_755_);
lean_dec_ref(v_val_753_);
v_toConstantVal_756_ = lean_ctor_get(v_val_754_, 0);
lean_inc_ref(v_toConstantVal_756_);
lean_dec_ref(v_val_754_);
v_fst_725_ = v_toConstantVal_755_;
v_snd_726_ = v_toConstantVal_756_;
goto v___jp_724_;
}
else
{
lean_dec(v_val_752_);
lean_dec_ref_known(v_val_741_, 1);
lean_dec_ref(v_b_712_);
goto v___jp_717_;
}
}
default: 
{
lean_dec_ref_known(v___x_746_, 1);
lean_dec(v_val_741_);
lean_dec_ref(v_b_712_);
goto v___jp_717_;
}
}
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
lean_dec(v___x_746_);
lean_dec(v_val_741_);
lean_dec_ref(v_b_712_);
v___x_757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_716_);
v___x_758_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_716_, v___x_713_);
v___x_759_ = lean_string_append(v___x_757_, v___x_758_);
lean_dec_ref(v___x_758_);
v___x_760_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 0);
lean_ctor_set(v___x_743_, 0, v___x_761_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v___x_740_);
lean_dec_ref(v_b_712_);
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_716_);
v___x_767_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_716_, v___x_713_);
v___x_768_ = lean_string_append(v___x_766_, v___x_767_);
lean_dec_ref(v___x_767_);
v___x_769_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_770_ = lean_string_append(v___x_768_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
v___jp_717_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0));
lean_inc(v_a_716_);
v___x_719_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_716_, v___x_713_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_722_ = lean_string_append(v___x_720_, v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
v___jp_724_:
{
uint8_t v___x_727_; 
v___x_727_ = l_Lean_instBEqConstantVal_beq(v_fst_725_, v_snd_726_);
lean_dec_ref(v_snd_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_fst_725_);
lean_dec_ref(v_b_712_);
v___x_728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1));
lean_inc(v_a_716_);
v___x_729_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_716_, v___x_713_);
v___x_730_ = lean_string_append(v___x_728_, v___x_729_);
lean_dec_ref(v___x_729_);
v___x_731_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_732_ = lean_string_append(v___x_730_, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_type_734_; lean_object* v___x_735_; lean_object* v___x_736_; size_t v___x_737_; size_t v___x_738_; 
v_type_734_ = lean_ctor_get(v_fst_725_, 2);
lean_inc_ref(v_type_734_);
lean_dec_ref(v_fst_725_);
v___x_735_ = l_Lean_Expr_getUsedConstants(v_type_734_);
v___x_736_ = l_Array_append___redArg(v_b_712_, v___x_735_);
lean_dec_ref(v___x_735_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_711_, v___x_737_);
v_i_711_ = v___x_738_;
v_b_712_ = v___x_736_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_challenge_707_ = stack[0].m_obj;
lean_object* v_solution_708_ = stack[1].m_obj;
lean_object* v_as_709_ = stack[2].m_obj;
size_t v_sz_710_ = stack[3].m_num;
size_t v_i_711_ = stack[4].m_num;
lean_object* v_b_712_ = stack[5].m_obj;
lean_object* v_res_772_;
v_res_772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_707_, v_solution_708_, v_as_709_, v_sz_710_, v_i_711_, v_b_712_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___boxed(lean_object* v_challenge_773_, lean_object* v_solution_774_, lean_object* v_as_775_, lean_object* v_sz_776_, lean_object* v_i_777_, lean_object* v_b_778_){
_start:
{
size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_sz_boxed_779_ = lean_unbox_usize(v_sz_776_);
lean_dec(v_sz_776_);
v_i_boxed_780_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_773_, v_solution_774_, v_as_775_, v_sz_boxed_779_, v_i_boxed_780_, v_b_778_);
lean_dec_ref(v_as_775_);
lean_dec_ref(v_solution_774_);
lean_dec_ref(v_challenge_773_);
return v_res_781_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__0(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_box(0);
v___x_783_ = lean_unsigned_to_nat(16u);
v___x_784_ = lean_mk_array(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_obj_once(&l_Lake_Check_compareAt___closed__0, &l_Lake_Check_compareAt___closed__0_once, _init_l_Lake_Check_compareAt___closed__0);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt(lean_object* v_challenge_788_, lean_object* v_solution_789_, lean_object* v_theoremTargets_790_, lean_object* v_definitionTargets_791_, lean_object* v_primitive_792_){
_start:
{
size_t v_sz_793_; size_t v___x_794_; lean_object* v___x_795_; 
v_sz_793_ = lean_array_size(v_theoremTargets_790_);
v___x_794_ = ((size_t)0ULL);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_788_, v_solution_789_, v_theoremTargets_790_, v_sz_793_, v___x_794_, v_primitive_792_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_solution_789_);
lean_dec_ref(v_challenge_788_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
else
{
lean_object* v_a_804_; size_t v_sz_805_; lean_object* v___x_806_; 
v_a_804_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_795_, 1);
v_sz_805_ = lean_array_size(v_definitionTargets_791_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_788_, v_solution_789_, v_definitionTargets_791_, v_sz_805_, v___x_794_, v_a_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_solution_789_);
lean_dec_ref(v_challenge_788_);
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_a_815_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_806_, 1);
v___x_816_ = lean_obj_once(&l_Lake_Check_compareAt___closed__1, &l_Lake_Check_compareAt___closed__1_once, _init_l_Lake_Check_compareAt___closed__1);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_816_, v_definitionTargets_791_);
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_816_, v_theoremTargets_790_);
v___x_819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_819_, 0, v_challenge_788_);
lean_ctor_set(v___x_819_, 1, v_solution_789_);
lean_ctor_set(v___x_819_, 2, v___x_817_);
lean_ctor_set(v___x_819_, 3, v___x_818_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_a_815_);
lean_ctor_set(v___x_820_, 1, v___x_816_);
v___x_821_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v___x_819_, v___x_820_);
lean_dec_ref_known(v___x_819_, 4);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_a_830_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_838_ == 0)
{
v___x_832_ = v___x_821_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_fst_834_; lean_object* v___x_836_; 
v_fst_834_ = lean_ctor_get(v_a_830_, 0);
lean_inc(v_fst_834_);
lean_dec(v_a_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v_fst_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_fst_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt___boxed(lean_object* v_challenge_839_, lean_object* v_solution_840_, lean_object* v_theoremTargets_841_, lean_object* v_definitionTargets_842_, lean_object* v_primitive_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lake_Check_compareAt(v_challenge_839_, v_solution_840_, v_theoremTargets_841_, v_definitionTargets_842_, v_primitive_843_);
lean_dec_ref(v_definitionTargets_842_);
lean_dec_ref(v_theoremTargets_841_);
return v_res_844_;
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
