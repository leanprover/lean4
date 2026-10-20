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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(lean_object* v_m_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_buckets_14_; lean_object* v___x_15_; uint64_t v___y_17_; 
v_buckets_14_ = lean_ctor_get(v_m_12_, 1);
v___x_15_ = lean_array_get_size(v_buckets_14_);
if (lean_obj_tag(v_a_13_) == 0)
{
uint64_t v___x_31_; 
v___x_31_ = 1723ULL;
v___y_17_ = v___x_31_;
goto v___jp_16_;
}
else
{
uint64_t v_hash_32_; 
v_hash_32_ = lean_ctor_get_uint64(v_a_13_, sizeof(void*)*2);
v___y_17_ = v_hash_32_;
goto v___jp_16_;
}
v___jp_16_:
{
uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v_fold_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_18_ = 32ULL;
v___x_19_ = lean_uint64_shift_right(v___y_17_, v___x_18_);
v_fold_20_ = lean_uint64_xor(v___y_17_, v___x_19_);
v___x_21_ = 16ULL;
v___x_22_ = lean_uint64_shift_right(v_fold_20_, v___x_21_);
v___x_23_ = lean_uint64_xor(v_fold_20_, v___x_22_);
v___x_24_ = lean_uint64_to_usize(v___x_23_);
v___x_25_ = lean_usize_of_nat(v___x_15_);
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_sub(v___x_25_, v___x_26_);
v___x_28_ = lean_usize_land(v___x_24_, v___x_27_);
v___x_29_ = lean_array_uget_borrowed(v_buckets_14_, v___x_28_);
v___x_30_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_13_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg___boxed(lean_object* v_m_33_, lean_object* v_a_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_m_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(lean_object* v_n_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_worklist_39_; lean_object* v_checked_40_; uint8_t v___x_41_; 
v_worklist_39_ = lean_ctor_get(v_a_38_, 0);
v_checked_40_ = lean_ctor_get(v_a_38_, 1);
v___x_41_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_40_, v_n_37_);
if (v___x_41_ == 0)
{
lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_52_; 
lean_inc_ref(v_checked_40_);
lean_inc_ref(v_worklist_39_);
v_isSharedCheck_52_ = !lean_is_exclusive(v_a_38_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; lean_object* v_unused_54_; 
v_unused_53_ = lean_ctor_get(v_a_38_, 1);
lean_dec(v_unused_53_);
v_unused_54_ = lean_ctor_get(v_a_38_, 0);
lean_dec(v_unused_54_);
v___x_43_ = v_a_38_;
v_isShared_44_ = v_isSharedCheck_52_;
goto v_resetjp_42_;
}
else
{
lean_dec(v_a_38_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_52_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_45_ = lean_box(0);
v___x_46_ = lean_array_push(v_worklist_39_, v_n_37_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_46_);
v___x_48_ = v___x_43_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_checked_40_);
v___x_48_ = v_reuseFailAlloc_51_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_45_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_dec(v_n_37_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v_a_38_);
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(lean_object* v_n_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(v_n_58_, v_a_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___boxed(lean_object* v_n_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist(v_n_62_, v_a_63_, v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(lean_object* v_00_u03b2_66_, lean_object* v_m_67_, lean_object* v_a_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_m_67_, v_a_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___boxed(lean_object* v_00_u03b2_70_, lean_object* v_m_71_, lean_object* v_a_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0(v_00_u03b2_70_, v_m_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_m_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(lean_object* v_00_u03b2_75_, lean_object* v_a_76_, lean_object* v_x_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_76_, v_x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_79_, lean_object* v_a_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0(v_00_u03b2_79_, v_a_80_, v_x_81_);
lean_dec(v_x_81_);
lean_dec(v_a_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(lean_object* v___x_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_84_);
lean_ctor_set(v___x_87_, 1, v___y_86_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0___boxed(lean_object* v___x_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___lam__0(v___x_89_, v___y_90_, v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(lean_object* v_f_93_, lean_object* v_as_94_, size_t v_i_95_, size_t v_stop_96_, lean_object* v_b_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = lean_usize_dec_eq(v_i_95_, v_stop_96_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_array_uget_borrowed(v_as_94_, v_i_95_);
lean_inc_ref(v_f_93_);
lean_inc_ref(v___y_98_);
lean_inc(v___x_101_);
v___x_102_ = lean_apply_3(v_f_93_, v___x_101_, v___y_98_, v___y_99_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_dec_ref(v_f_93_);
return v___x_102_;
}
else
{
lean_object* v_a_103_; lean_object* v_fst_104_; lean_object* v_snd_105_; size_t v___x_106_; size_t v___x_107_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v_fst_104_ = lean_ctor_get(v_a_103_, 0);
lean_inc(v_fst_104_);
v_snd_105_ = lean_ctor_get(v_a_103_, 1);
lean_inc(v_snd_105_);
lean_dec(v_a_103_);
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_95_, v___x_106_);
v_i_95_ = v___x_107_;
v_b_97_ = v_fst_104_;
v___y_99_ = v_snd_105_;
goto _start;
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec_ref(v_f_93_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_b_97_);
lean_ctor_set(v___x_109_, 1, v___y_99_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed(lean_object* v_f_111_, lean_object* v_as_112_, lean_object* v_i_113_, lean_object* v_stop_114_, lean_object* v_b_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_113_);
lean_dec(v_i_113_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_114_);
lean_dec(v_stop_114_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_111_, v_as_112_, v_i_boxed_118_, v_stop_boxed_119_, v_b_115_, v___y_116_, v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec_ref(v_as_112_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(lean_object* v_f_121_, lean_object* v_as_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
if (lean_obj_tag(v_as_122_) == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref(v_f_121_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___y_124_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_tail_129_; lean_object* v___x_130_; 
v_head_128_ = lean_ctor_get(v_as_122_, 0);
lean_inc(v_head_128_);
v_tail_129_ = lean_ctor_get(v_as_122_, 1);
lean_inc(v_tail_129_);
lean_dec_ref_known(v_as_122_, 2);
lean_inc_ref(v_f_121_);
lean_inc_ref(v___y_123_);
v___x_130_ = lean_apply_3(v_f_121_, v_head_128_, v___y_123_, v___y_124_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_dec(v_tail_129_);
lean_dec_ref(v_f_121_);
return v___x_130_;
}
else
{
lean_object* v_a_131_; lean_object* v_snd_132_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v_snd_132_ = lean_ctor_get(v_a_131_, 1);
lean_inc(v_snd_132_);
lean_dec(v_a_131_);
v_as_122_ = v_tail_129_;
v___y_124_ = v_snd_132_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1___boxed(lean_object* v_f_134_, lean_object* v_as_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_134_, v_as_135_, v___y_136_, v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(lean_object* v_f_139_, lean_object* v_as_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
if (lean_obj_tag(v_as_140_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_f_139_);
v___x_143_ = lean_box(0);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___y_142_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
else
{
lean_object* v_head_146_; lean_object* v_tail_147_; lean_object* v_ctor_148_; lean_object* v_rhs_149_; lean_object* v___x_150_; 
v_head_146_ = lean_ctor_get(v_as_140_, 0);
lean_inc(v_head_146_);
v_tail_147_ = lean_ctor_get(v_as_140_, 1);
lean_inc(v_tail_147_);
lean_dec_ref_known(v_as_140_, 2);
v_ctor_148_ = lean_ctor_get(v_head_146_, 0);
lean_inc(v_ctor_148_);
v_rhs_149_ = lean_ctor_get(v_head_146_, 2);
lean_inc_ref(v_rhs_149_);
lean_dec(v_head_146_);
lean_inc_ref(v_f_139_);
lean_inc_ref(v___y_141_);
v___x_150_ = lean_apply_3(v_f_139_, v_ctor_148_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_dec_ref(v_rhs_149_);
lean_dec(v_tail_147_);
lean_dec_ref(v_f_139_);
return v___x_150_;
}
else
{
lean_object* v_a_151_; lean_object* v_snd_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v_snd_152_ = lean_ctor_get(v_a_151_, 1);
lean_inc(v_snd_152_);
lean_dec(v_a_151_);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_Expr_getUsedConstants(v_rhs_149_);
v___x_155_ = lean_array_get_size(v___x_154_);
v___x_156_ = lean_nat_dec_lt(v___x_153_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec_ref(v___x_154_);
v_as_140_ = v_tail_147_;
v___y_142_ = v_snd_152_;
goto _start;
}
else
{
lean_object* v___x_158_; size_t v___x_159_; size_t v___x_160_; lean_object* v___x_161_; 
v___x_158_ = lean_box(0);
v___x_159_ = ((size_t)0ULL);
v___x_160_ = lean_usize_of_nat(v___x_155_);
lean_inc_ref(v_f_139_);
v___x_161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_139_, v___x_154_, v___x_159_, v___x_160_, v___x_158_, v___y_141_, v_snd_152_);
lean_dec_ref(v___x_154_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_dec(v_tail_147_);
lean_dec_ref(v_f_139_);
return v___x_161_;
}
else
{
lean_object* v_a_162_; lean_object* v_snd_163_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_162_);
lean_dec_ref_known(v___x_161_, 1);
v_snd_163_ = lean_ctor_get(v_a_162_, 1);
lean_inc(v_snd_163_);
lean_dec(v_a_162_);
v_as_140_ = v_tail_147_;
v___y_142_ = v_snd_163_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2___boxed(lean_object* v_f_165_, lean_object* v_as_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(v_f_165_, v_as_166_, v___y_167_, v___y_168_);
lean_dec_ref(v___y_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(lean_object* v_info_174_, lean_object* v_f_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___y_201_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_197_ = l_Lean_ConstantInfo_type(v_info_174_);
v___x_198_ = l_Lean_Expr_getUsedConstants(v___x_197_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_array_get_size(v___x_198_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_nat_dec_lt(v___x_199_, v___x_221_);
if (v___x_223_ == 0)
{
lean_object* v___f_224_; 
lean_dec_ref(v___x_198_);
v___f_224_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___closed__0));
v___y_201_ = v___f_224_;
goto v___jp_200_;
}
else
{
size_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_225_ = lean_usize_of_nat(v___x_221_);
v___x_226_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed__const__1));
v___x_227_ = lean_box_usize(v___x_225_);
lean_inc_ref(v_f_175_);
v___x_228_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0___boxed), 7, 5);
lean_closure_set(v___x_228_, 0, v_f_175_);
lean_closure_set(v___x_228_, 1, v___x_198_);
lean_closure_set(v___x_228_, 2, v___x_226_);
lean_closure_set(v___x_228_, 3, v___x_227_);
lean_closure_set(v___x_228_, 4, v___x_222_);
v___y_201_ = v___x_228_;
goto v___jp_200_;
}
v___jp_178_:
{
switch(lean_obj_tag(v_info_174_))
{
case 5:
{
lean_object* v_val_181_; lean_object* v_all_182_; lean_object* v_ctors_183_; lean_object* v___x_184_; 
v_val_181_ = lean_ctor_get(v_info_174_, 0);
lean_inc_ref(v_val_181_);
lean_dec_ref_known(v_info_174_, 1);
v_all_182_ = lean_ctor_get(v_val_181_, 3);
lean_inc(v_all_182_);
v_ctors_183_ = lean_ctor_get(v_val_181_, 4);
lean_inc(v_ctors_183_);
lean_dec_ref(v_val_181_);
lean_inc_ref(v_f_175_);
v___x_184_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_175_, v_ctors_183_, v___y_179_, v___y_180_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_dec(v_all_182_);
lean_dec_ref(v_f_175_);
return v___x_184_;
}
else
{
lean_object* v_a_185_; lean_object* v_snd_186_; lean_object* v___x_187_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v_snd_186_ = lean_ctor_get(v_a_185_, 1);
lean_inc(v_snd_186_);
lean_dec(v_a_185_);
v___x_187_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__1(v_f_175_, v_all_182_, v___y_179_, v_snd_186_);
return v___x_187_;
}
}
case 6:
{
lean_object* v_val_188_; lean_object* v_induct_189_; lean_object* v___x_190_; 
v_val_188_ = lean_ctor_get(v_info_174_, 0);
lean_inc_ref(v_val_188_);
lean_dec_ref_known(v_info_174_, 1);
v_induct_189_ = lean_ctor_get(v_val_188_, 1);
lean_inc(v_induct_189_);
lean_dec_ref(v_val_188_);
lean_inc_ref(v___y_179_);
v___x_190_ = lean_apply_3(v_f_175_, v_induct_189_, v___y_179_, v___y_180_);
return v___x_190_;
}
case 7:
{
lean_object* v_val_191_; lean_object* v_rules_192_; lean_object* v___x_193_; 
v_val_191_ = lean_ctor_get(v_info_174_, 0);
lean_inc_ref(v_val_191_);
lean_dec_ref_known(v_info_174_, 1);
v_rules_192_ = lean_ctor_get(v_val_191_, 6);
lean_inc(v_rules_192_);
lean_dec_ref(v_val_191_);
v___x_193_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__2(v_f_175_, v_rules_192_, v___y_179_, v___y_180_);
return v___x_193_;
}
default: 
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec_ref(v_f_175_);
lean_dec_ref(v_info_174_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___y_180_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
}
v___jp_200_:
{
lean_object* v___x_202_; 
lean_inc_ref(v___y_176_);
v___x_202_ = lean_apply_2(v___y_201_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_dec_ref(v_f_175_);
lean_dec_ref(v_info_174_);
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v_snd_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_snd_204_ = lean_ctor_get(v_a_203_, 1);
lean_inc(v_snd_204_);
lean_dec(v_a_203_);
v___x_205_ = l_Lean_ConstantInfo_name(v_info_174_);
lean_inc_ref(v_f_175_);
lean_inc_ref(v___y_176_);
v___x_206_ = lean_apply_3(v_f_175_, v___x_205_, v___y_176_, v_snd_204_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_dec_ref(v_f_175_);
lean_dec_ref(v_info_174_);
return v___x_206_;
}
else
{
lean_object* v_a_207_; lean_object* v_snd_208_; uint8_t v___x_209_; lean_object* v___x_210_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v_snd_208_ = lean_ctor_get(v_a_207_, 1);
lean_inc(v_snd_208_);
lean_dec(v_a_207_);
v___x_209_ = 1;
lean_inc_ref(v_info_174_);
v___x_210_ = l_Lean_ConstantInfo_value_x3f(v_info_174_, v___x_209_);
if (lean_obj_tag(v___x_210_) == 1)
{
lean_object* v_val_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_val_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v___x_210_, 1);
v___x_212_ = l_Lean_Expr_getUsedConstants(v_val_211_);
v___x_213_ = lean_array_get_size(v___x_212_);
v___x_214_ = lean_nat_dec_lt(v___x_199_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec_ref(v___x_212_);
v___y_179_ = v___y_176_;
v___y_180_ = v_snd_208_;
goto v___jp_178_;
}
else
{
lean_object* v___x_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; 
v___x_215_ = lean_box(0);
v___x_216_ = ((size_t)0ULL);
v___x_217_ = lean_usize_of_nat(v___x_213_);
lean_inc_ref(v_f_175_);
v___x_218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0_spec__0(v_f_175_, v___x_212_, v___x_216_, v___x_217_, v___x_215_, v___y_176_, v_snd_208_);
lean_dec_ref(v___x_212_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_dec_ref(v_f_175_);
lean_dec_ref(v_info_174_);
return v___x_218_;
}
else
{
lean_object* v_a_219_; lean_object* v_snd_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v_snd_220_ = lean_ctor_get(v_a_219_, 1);
lean_inc(v_snd_220_);
lean_dec(v_a_219_);
v___y_179_ = v___y_176_;
v___y_180_ = v_snd_220_;
goto v___jp_178_;
}
}
}
else
{
lean_dec(v___x_210_);
v___y_179_ = v___y_176_;
v___y_180_ = v_snd_208_;
goto v___jp_178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0___boxed(lean_object* v_info_229_, lean_object* v_f_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(v_info_229_, v_f_230_, v___y_231_, v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(lean_object* v_info_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___closed__0));
v___x_239_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts_spec__0(v_info_235_, v___x_238_, v_a_236_, v_a_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts___boxed(lean_object* v_info_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_info_240_, v_a_241_, v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(lean_object* v_a_244_, lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_box(0);
return v___x_246_;
}
else
{
lean_object* v_key_247_; lean_object* v_value_248_; lean_object* v_tail_249_; uint8_t v___x_250_; 
v_key_247_ = lean_ctor_get(v_x_245_, 0);
v_value_248_ = lean_ctor_get(v_x_245_, 1);
v_tail_249_ = lean_ctor_get(v_x_245_, 2);
v___x_250_ = lean_name_eq(v_key_247_, v_a_244_);
if (v___x_250_ == 0)
{
v_x_245_ = v_tail_249_;
goto _start;
}
else
{
lean_object* v___x_252_; 
lean_inc(v_value_248_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v_value_248_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg___boxed(lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_253_, v_x_254_);
lean_dec(v_x_254_);
lean_dec(v_a_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(lean_object* v_m_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_buckets_258_; lean_object* v___x_259_; uint64_t v___y_261_; 
v_buckets_258_ = lean_ctor_get(v_m_256_, 1);
v___x_259_ = lean_array_get_size(v_buckets_258_);
if (lean_obj_tag(v_a_257_) == 0)
{
uint64_t v___x_275_; 
v___x_275_ = 1723ULL;
v___y_261_ = v___x_275_;
goto v___jp_260_;
}
else
{
uint64_t v_hash_276_; 
v_hash_276_ = lean_ctor_get_uint64(v_a_257_, sizeof(void*)*2);
v___y_261_ = v_hash_276_;
goto v___jp_260_;
}
v___jp_260_:
{
uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v_fold_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_262_ = 32ULL;
v___x_263_ = lean_uint64_shift_right(v___y_261_, v___x_262_);
v_fold_264_ = lean_uint64_xor(v___y_261_, v___x_263_);
v___x_265_ = 16ULL;
v___x_266_ = lean_uint64_shift_right(v_fold_264_, v___x_265_);
v___x_267_ = lean_uint64_xor(v_fold_264_, v___x_266_);
v___x_268_ = lean_uint64_to_usize(v___x_267_);
v___x_269_ = lean_usize_of_nat(v___x_259_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_sub(v___x_269_, v___x_270_);
v___x_272_ = lean_usize_land(v___x_268_, v___x_271_);
v___x_273_ = lean_array_uget_borrowed(v_buckets_258_, v___x_272_);
v___x_274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_257_, v___x_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg___boxed(lean_object* v_m_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_277_, v_a_278_);
lean_dec(v_a_278_);
lean_dec_ref(v_m_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
if (lean_obj_tag(v_x_281_) == 0)
{
return v_x_280_;
}
else
{
lean_object* v_key_282_; lean_object* v_value_283_; lean_object* v_tail_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_310_; 
v_key_282_ = lean_ctor_get(v_x_281_, 0);
v_value_283_ = lean_ctor_get(v_x_281_, 1);
v_tail_284_ = lean_ctor_get(v_x_281_, 2);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_310_ == 0)
{
v___x_286_ = v_x_281_;
v_isShared_287_ = v_isSharedCheck_310_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_tail_284_);
lean_inc(v_value_283_);
lean_inc(v_key_282_);
lean_dec(v_x_281_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_310_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; uint64_t v___y_290_; 
v___x_288_ = lean_array_get_size(v_x_280_);
if (lean_obj_tag(v_key_282_) == 0)
{
uint64_t v___x_308_; 
v___x_308_ = 1723ULL;
v___y_290_ = v___x_308_;
goto v___jp_289_;
}
else
{
uint64_t v_hash_309_; 
v_hash_309_ = lean_ctor_get_uint64(v_key_282_, sizeof(void*)*2);
v___y_290_ = v_hash_309_;
goto v___jp_289_;
}
v___jp_289_:
{
uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_291_ = 32ULL;
v___x_292_ = lean_uint64_shift_right(v___y_290_, v___x_291_);
v_fold_293_ = lean_uint64_xor(v___y_290_, v___x_292_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_288_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v___x_302_ = lean_array_uget_borrowed(v_x_280_, v___x_301_);
lean_inc(v___x_302_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 2, v___x_302_);
v___x_304_ = v___x_286_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_key_282_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_value_283_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v___x_302_);
v___x_304_ = v_reuseFailAlloc_307_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_array_uset(v_x_280_, v___x_301_, v___x_304_);
v_x_280_ = v___x_305_;
v_x_281_ = v_tail_284_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(lean_object* v_i_311_, lean_object* v_source_312_, lean_object* v_target_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_array_get_size(v_source_312_);
v___x_315_ = lean_nat_dec_lt(v_i_311_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_source_312_);
lean_dec(v_i_311_);
return v_target_313_;
}
else
{
lean_object* v_es_316_; lean_object* v___x_317_; lean_object* v_source_318_; lean_object* v_target_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_es_316_ = lean_array_fget(v_source_312_, v_i_311_);
v___x_317_ = lean_box(0);
v_source_318_ = lean_array_fset(v_source_312_, v_i_311_, v___x_317_);
v_target_319_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_target_313_, v_es_316_);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_i_311_, v___x_320_);
lean_dec(v_i_311_);
v_i_311_ = v___x_321_;
v_source_312_ = v_source_318_;
v_target_313_ = v_target_319_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(lean_object* v_data_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_nbuckets_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_324_ = lean_array_get_size(v_data_323_);
v___x_325_ = lean_unsigned_to_nat(2u);
v_nbuckets_326_ = lean_nat_mul(v___x_324_, v___x_325_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_box(0);
v___x_329_ = lean_mk_array(v_nbuckets_326_, v___x_328_);
v___x_330_ = lean_array_propagate_mark(v_data_323_, v___x_329_);
v___x_331_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v___x_327_, v_data_323_, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(lean_object* v_m_332_, lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
lean_object* v_size_335_; lean_object* v_buckets_336_; lean_object* v___x_337_; uint64_t v___y_339_; 
v_size_335_ = lean_ctor_get(v_m_332_, 0);
v_buckets_336_ = lean_ctor_get(v_m_332_, 1);
v___x_337_ = lean_array_get_size(v_buckets_336_);
if (lean_obj_tag(v_a_333_) == 0)
{
uint64_t v___x_376_; 
v___x_376_ = 1723ULL;
v___y_339_ = v___x_376_;
goto v___jp_338_;
}
else
{
uint64_t v_hash_377_; 
v_hash_377_ = lean_ctor_get_uint64(v_a_333_, sizeof(void*)*2);
v___y_339_ = v_hash_377_;
goto v___jp_338_;
}
v___jp_338_:
{
uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_bkt_351_; uint8_t v___x_352_; 
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___y_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___y_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_337_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v_bkt_351_ = lean_array_uget_borrowed(v_buckets_336_, v___x_350_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0_spec__0___redArg(v_a_333_, v_bkt_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_373_; 
lean_inc_ref(v_buckets_336_);
lean_inc(v_size_335_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_m_332_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; lean_object* v_unused_375_; 
v_unused_374_ = lean_ctor_get(v_m_332_, 1);
lean_dec(v_unused_374_);
v_unused_375_ = lean_ctor_get(v_m_332_, 0);
lean_dec(v_unused_375_);
v___x_354_ = v_m_332_;
v_isShared_355_ = v_isSharedCheck_373_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_m_332_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_373_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v_size_x27_357_; lean_object* v___x_358_; lean_object* v_buckets_x27_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v_size_x27_357_ = lean_nat_add(v_size_335_, v___x_356_);
lean_dec(v_size_335_);
lean_inc(v_bkt_351_);
v___x_358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_358_, 0, v_a_333_);
lean_ctor_set(v___x_358_, 1, v_b_334_);
lean_ctor_set(v___x_358_, 2, v_bkt_351_);
v_buckets_x27_359_ = lean_array_uset(v_buckets_336_, v___x_350_, v___x_358_);
v___x_360_ = lean_unsigned_to_nat(4u);
v___x_361_ = lean_nat_mul(v_size_x27_357_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(3u);
v___x_363_ = lean_nat_div(v___x_361_, v___x_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_array_get_size(v_buckets_x27_359_);
v___x_365_ = lean_nat_dec_le(v___x_363_, v___x_364_);
lean_dec(v___x_363_);
if (v___x_365_ == 0)
{
lean_object* v_val_366_; lean_object* v___x_368_; 
v_val_366_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_buckets_x27_359_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_val_366_);
lean_ctor_set(v___x_354_, 0, v_size_x27_357_);
v___x_368_ = v___x_354_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_x27_357_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_val_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v___x_371_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_buckets_x27_359_);
lean_ctor_set(v___x_354_, 0, v_size_x27_357_);
v___x_371_ = v___x_354_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_x27_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_buckets_x27_359_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_dec(v_b_334_);
lean_dec(v_a_333_);
return v_m_332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(lean_object* v_as_378_, size_t v_i_379_, size_t v_stop_380_, lean_object* v_b_381_, lean_object* v___y_382_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = lean_usize_dec_eq(v_i_379_, v_stop_380_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_array_uget_borrowed(v_as_378_, v_i_379_);
lean_inc(v___x_384_);
v___x_385_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist___redArg(v___x_384_, v___y_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v_fst_387_; lean_object* v_snd_388_; size_t v___x_389_; size_t v___x_390_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v_fst_387_ = lean_ctor_get(v_a_386_, 0);
lean_inc(v_fst_387_);
v_snd_388_ = lean_ctor_get(v_a_386_, 1);
lean_inc(v_snd_388_);
lean_dec(v_a_386_);
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_add(v_i_379_, v___x_389_);
v_i_379_ = v___x_390_;
v_b_381_ = v_fst_387_;
v___y_382_ = v_snd_388_;
goto _start;
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_b_381_);
lean_ctor_set(v___x_392_, 1, v___y_382_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg___boxed(lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_stop_396_, lean_object* v_b_397_, lean_object* v___y_398_){
_start:
{
size_t v_i_boxed_399_; size_t v_stop_boxed_400_; lean_object* v_res_401_; 
v_i_boxed_399_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_stop_boxed_400_ = lean_unbox_usize(v_stop_396_);
lean_dec(v_stop_396_);
v_res_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_394_, v_i_boxed_399_, v_stop_boxed_400_, v_b_397_, v___y_398_);
lean_dec_ref(v_as_394_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_worklist_408_; lean_object* v_checked_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_worklist_408_ = lean_ctor_get(v_a_407_, 0);
v_checked_409_ = lean_ctor_get(v_a_407_, 1);
v___x_410_ = lean_array_get_size(v_worklist_408_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_nat_dec_eq(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_500_; 
lean_inc_ref(v_checked_409_);
lean_inc_ref(v_worklist_408_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; 
v_unused_501_ = lean_ctor_get(v_a_407_, 1);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_a_407_, 0);
lean_dec(v_unused_502_);
v___x_414_ = v_a_407_;
v_isShared_415_ = v_isSharedCheck_500_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_a_407_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_500_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___y_421_; lean_object* v_worklist_422_; lean_object* v_checked_423_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_sub(v___x_410_, v___x_417_);
v___x_419_ = lean_array_get(v___x_416_, v_worklist_408_, v___x_418_);
lean_dec(v___x_418_);
v___x_435_ = lean_array_pop(v_worklist_408_);
lean_inc_ref(v_checked_409_);
lean_inc_ref(v___x_435_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v_checked_409_);
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_409_, v___x_419_);
if (v___x_437_ == 0)
{
lean_object* v_challenge_438_; lean_object* v_solution_439_; lean_object* v_definitionTargets_440_; lean_object* v_theoremTargets_441_; lean_object* v_constMap_442_; lean_object* v___x_443_; 
v_challenge_438_ = lean_ctor_get(v_a_406_, 0);
v_solution_439_ = lean_ctor_get(v_a_406_, 1);
v_definitionTargets_440_ = lean_ctor_get(v_a_406_, 2);
v_theoremTargets_441_ = lean_ctor_get(v_a_406_, 3);
v_constMap_442_ = lean_ctor_get(v_challenge_438_, 0);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_442_, v___x_419_);
if (lean_obj_tag(v___x_443_) == 1)
{
lean_object* v_val_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_491_; 
v_val_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_491_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_491_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_val_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_491_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_constMap_448_; lean_object* v___x_449_; 
v_constMap_448_ = lean_ctor_get(v_solution_439_, 0);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_448_, v___x_419_);
if (lean_obj_tag(v___x_449_) == 1)
{
lean_object* v_val_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_446_);
v_val_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_481_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_481_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_val_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_481_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = l_Lean_ConstantInfo_name(v_val_450_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_definitionTargets_440_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_theoremTargets_441_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_467_ == 0)
{
uint8_t v___x_468_; 
lean_dec_ref(v___x_435_);
lean_dec_ref(v_checked_409_);
v___x_468_ = l_Lean_instBEqConstantInfo_beq(v_val_444_, v_val_450_);
lean_dec(v_val_444_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
lean_dec(v_val_450_);
lean_dec_ref_known(v___x_436_, 2);
lean_del_object(v___x_414_);
v___x_469_ = 1;
v___x_470_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
v___x_471_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_419_, v___x_469_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 0);
lean_ctor_set(v___x_452_, 0, v___x_474_);
v___x_476_ = v___x_452_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_478_; 
lean_del_object(v___x_452_);
v___x_478_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_val_450_, v_a_406_, v___x_436_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_dec(v___x_419_);
lean_del_object(v___x_414_);
return v___x_478_;
}
else
{
lean_object* v_a_479_; lean_object* v_snd_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_snd_480_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_snd_480_);
lean_dec(v_a_479_);
v___y_431_ = v_a_406_;
v___y_432_ = v_snd_480_;
goto v___jp_430_;
}
}
}
else
{
lean_del_object(v___x_452_);
lean_dec(v_val_444_);
goto v___jp_454_;
}
}
else
{
lean_dec(v___x_465_);
lean_del_object(v___x_452_);
lean_dec(v_val_444_);
goto v___jp_454_;
}
v___jp_454_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_455_ = l_Lean_ConstantInfo_type(v_val_450_);
lean_dec(v_val_450_);
v___x_456_ = l_Lean_Expr_getUsedConstants(v___x_455_);
v___x_457_ = lean_array_get_size(v___x_456_);
v___x_458_ = lean_nat_dec_lt(v___x_411_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec_ref(v___x_456_);
lean_dec_ref_known(v___x_436_, 2);
v___y_421_ = v_a_406_;
v_worklist_422_ = v___x_435_;
v_checked_423_ = v_checked_409_;
goto v___jp_420_;
}
else
{
lean_object* v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; 
lean_dec_ref(v___x_435_);
lean_dec_ref(v_checked_409_);
v___x_459_ = lean_box(0);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = lean_usize_of_nat(v___x_457_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_456_, v___x_460_, v___x_461_, v___x_459_, v___x_436_);
lean_dec_ref(v___x_456_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_dec(v___x_419_);
lean_del_object(v___x_414_);
return v___x_462_;
}
else
{
lean_object* v_a_463_; lean_object* v_snd_464_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v_snd_464_ = lean_ctor_get(v_a_463_, 1);
lean_inc(v_snd_464_);
lean_dec(v_a_463_);
v___y_431_ = v_a_406_;
v___y_432_ = v_snd_464_;
goto v___jp_430_;
}
}
}
}
}
else
{
lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
lean_dec(v___x_449_);
lean_dec(v_val_444_);
lean_dec_ref_known(v___x_436_, 2);
lean_dec_ref(v___x_435_);
lean_del_object(v___x_414_);
lean_dec_ref(v_checked_409_);
v___x_482_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2));
v___x_483_ = 1;
v___x_484_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_419_, v___x_483_);
v___x_485_ = lean_string_append(v___x_482_, v___x_484_);
lean_dec_ref(v___x_484_);
v___x_486_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_487_ = lean_string_append(v___x_485_, v___x_486_);
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
lean_ctor_set(v___x_446_, 0, v___x_487_);
v___x_489_ = v___x_446_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
else
{
lean_object* v___x_492_; uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v___x_443_);
lean_dec_ref_known(v___x_436_, 2);
lean_dec_ref(v___x_435_);
lean_del_object(v___x_414_);
lean_dec_ref(v_checked_409_);
v___x_492_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3));
v___x_493_ = 1;
v___x_494_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_419_, v___x_493_);
v___x_495_ = lean_string_append(v___x_492_, v___x_494_);
lean_dec_ref(v___x_494_);
v___x_496_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_497_ = lean_string_append(v___x_495_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
else
{
lean_dec_ref(v___x_435_);
lean_dec(v___x_419_);
lean_del_object(v___x_414_);
lean_dec_ref(v_checked_409_);
v_a_407_ = v___x_436_;
goto _start;
}
v___jp_420_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_424_ = lean_box(0);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_checked_423_, v___x_419_, v___x_424_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_425_);
lean_ctor_set(v___x_414_, 0, v_worklist_422_);
v___x_427_ = v___x_414_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_worklist_422_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_429_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
v_a_406_ = v___y_421_;
v_a_407_ = v___x_427_;
goto _start;
}
}
v___jp_430_:
{
lean_object* v_worklist_433_; lean_object* v_checked_434_; 
v_worklist_433_ = lean_ctor_get(v___y_432_, 0);
lean_inc_ref(v_worklist_433_);
v_checked_434_ = lean_ctor_get(v___y_432_, 1);
lean_inc_ref(v_checked_434_);
lean_dec_ref(v___y_432_);
v___y_421_ = v___y_431_;
v_worklist_422_ = v_worklist_433_;
v_checked_423_ = v_checked_434_;
goto v___jp_420_;
}
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v_a_407_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___boxed(lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v_a_506_, v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_a_511_, lean_object* v_b_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_m_510_, v_a_511_, v_b_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_515_, v_a_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___boxed(lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(v_00_u03b2_518_, v_m_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_m_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(lean_object* v_as_522_, size_t v_i_523_, size_t v_stop_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_522_, v_i_523_, v_stop_524_, v_b_525_, v___y_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___boxed(lean_object* v_as_529_, lean_object* v_i_530_, lean_object* v_stop_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_530_);
lean_dec(v_i_530_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_531_);
lean_dec(v_stop_531_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(v_as_529_, v_i_boxed_535_, v_stop_boxed_536_, v_b_532_, v___y_533_, v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v_as_529_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0(lean_object* v_00_u03b2_538_, lean_object* v_data_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_data_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(lean_object* v_00_u03b2_541_, lean_object* v_a_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_542_, v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___boxed(lean_object* v_00_u03b2_545_, lean_object* v_a_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(v_00_u03b2_545_, v_a_546_, v_x_547_);
lean_dec(v_x_547_);
lean_dec(v_a_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_549_, lean_object* v_i_550_, lean_object* v_source_551_, lean_object* v_target_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v_i_550_, v_source_551_, v_target_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_x_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT uint8_t l_Lake_Check_definitionHoleMatches(lean_object* v_challengeHole_558_, lean_object* v_solutionHole_559_){
_start:
{
lean_object* v_toConstantVal_560_; uint8_t v_safety_561_; lean_object* v_toConstantVal_562_; uint8_t v_safety_563_; uint8_t v___x_564_; 
v_toConstantVal_560_ = lean_ctor_get(v_challengeHole_558_, 0);
v_safety_561_ = lean_ctor_get_uint8(v_challengeHole_558_, sizeof(void*)*4);
v_toConstantVal_562_ = lean_ctor_get(v_solutionHole_559_, 0);
v_safety_563_ = lean_ctor_get_uint8(v_solutionHole_559_, sizeof(void*)*4);
v___x_564_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_560_, v_toConstantVal_562_);
if (v___x_564_ == 0)
{
return v___x_564_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_561_, v_safety_563_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_definitionHoleMatches___boxed(lean_object* v_challengeHole_566_, lean_object* v_solutionHole_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lake_Check_definitionHoleMatches(v_challengeHole_566_, v_solutionHole_567_);
lean_dec_ref(v_solutionHole_567_);
lean_dec_ref(v_challengeHole_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(lean_object* v_as_570_, size_t v_sz_571_, size_t v_i_572_, lean_object* v_b_573_){
_start:
{
uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_lt(v_i_572_, v_sz_571_);
if (v___x_574_ == 0)
{
return v_b_573_;
}
else
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v_r_577_; size_t v___x_578_; size_t v___x_579_; 
v_a_575_ = lean_array_uget_borrowed(v_as_570_, v_i_572_);
v___x_576_ = lean_box(0);
lean_inc(v_a_575_);
v_r_577_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_b_573_, v_a_575_, v___x_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_572_, v___x_578_);
v_i_572_ = v___x_579_;
v_b_573_ = v_r_577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2___boxed(lean_object* v_as_581_, lean_object* v_sz_582_, lean_object* v_i_583_, lean_object* v_b_584_){
_start:
{
size_t v_sz_boxed_585_; size_t v_i_boxed_586_; lean_object* v_res_587_; 
v_sz_boxed_585_ = lean_unbox_usize(v_sz_582_);
lean_dec(v_sz_582_);
v_i_boxed_586_ = lean_unbox_usize(v_i_583_);
lean_dec(v_i_583_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_as_581_, v_sz_boxed_585_, v_i_boxed_586_, v_b_584_);
lean_dec_ref(v_as_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(lean_object* v_m_588_, lean_object* v_l_589_){
_start:
{
size_t v_sz_590_; size_t v___x_591_; lean_object* v___x_592_; 
v_sz_590_ = lean_array_size(v_l_589_);
v___x_591_ = ((size_t)0ULL);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_l_589_, v_sz_590_, v___x_591_, v_m_588_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2___boxed(lean_object* v_m_593_, lean_object* v_l_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v_m_593_, v_l_594_);
lean_dec_ref(v_l_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(lean_object* v_challenge_600_, lean_object* v_solution_601_, lean_object* v_as_602_, size_t v_sz_603_, size_t v_i_604_, lean_object* v_b_605_){
_start:
{
uint8_t v___x_606_; 
v___x_606_ = lean_usize_dec_lt(v_i_604_, v_sz_603_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v_b_605_);
return v___x_607_;
}
else
{
lean_object* v_constMap_608_; lean_object* v_a_609_; lean_object* v___x_610_; 
v_constMap_608_ = lean_ctor_get(v_challenge_600_, 0);
v_a_609_ = lean_array_uget_borrowed(v_as_602_, v_i_604_);
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_608_, v_a_609_);
if (lean_obj_tag(v___x_610_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_673_; 
v_val_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_673_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_673_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_val_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_673_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_constMap_615_; lean_object* v___x_616_; 
v_constMap_615_ = lean_ctor_get(v_solution_601_, 0);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_615_, v_a_609_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_del_object(v___x_613_);
if (lean_obj_tag(v_val_611_) == 1)
{
lean_object* v_val_617_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v___x_616_, 1);
if (lean_obj_tag(v_val_617_) == 1)
{
lean_object* v_val_618_; lean_object* v_val_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_638_; 
v_val_618_ = lean_ctor_get(v_val_611_, 0);
lean_inc_ref(v_val_618_);
lean_dec_ref_known(v_val_611_, 1);
v_val_619_ = lean_ctor_get(v_val_617_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v_val_617_);
if (v_isSharedCheck_638_ == 0)
{
v___x_621_ = v_val_617_;
v_isShared_622_ = v_isSharedCheck_638_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_val_619_);
lean_dec(v_val_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_638_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; 
v___x_623_ = l_Lake_Check_definitionHoleMatches(v_val_618_, v_val_619_);
lean_dec_ref(v_val_618_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
lean_dec_ref(v_val_619_);
lean_dec_ref(v_b_605_);
v___x_624_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
lean_inc(v_a_609_);
v___x_625_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_609_, v___x_606_);
v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
lean_dec_ref(v___x_625_);
v___x_627_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_628_ = lean_string_append(v___x_626_, v___x_627_);
if (v_isShared_622_ == 0)
{
lean_ctor_set_tag(v___x_621_, 0);
lean_ctor_set(v___x_621_, 0, v___x_628_);
v___x_630_ = v___x_621_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v_toConstantVal_632_; lean_object* v_name_633_; lean_object* v___x_634_; size_t v___x_635_; size_t v___x_636_; 
lean_del_object(v___x_621_);
v_toConstantVal_632_ = lean_ctor_get(v_val_619_, 0);
lean_inc_ref(v_toConstantVal_632_);
lean_dec_ref(v_val_619_);
v_name_633_ = lean_ctor_get(v_toConstantVal_632_, 0);
lean_inc(v_name_633_);
lean_dec_ref(v_toConstantVal_632_);
v___x_634_ = lean_array_push(v_b_605_, v_name_633_);
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_add(v_i_604_, v___x_635_);
v_i_604_ = v___x_636_;
v_b_605_ = v___x_634_;
goto _start;
}
}
}
else
{
lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_val_617_);
lean_dec_ref(v_b_605_);
v_isSharedCheck_650_ = !lean_is_exclusive(v_val_611_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_val_611_, 0);
lean_dec(v_unused_651_);
v___x_640_ = v_val_611_;
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
else
{
lean_dec(v_val_611_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_650_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0));
lean_inc(v_a_609_);
v___x_643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_609_, v___x_606_);
v___x_644_ = lean_string_append(v___x_642_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
if (v_isShared_641_ == 0)
{
lean_ctor_set_tag(v___x_640_, 0);
lean_ctor_set(v___x_640_, 0, v___x_646_);
v___x_648_ = v___x_640_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_val_611_);
lean_dec_ref(v_b_605_);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v___x_616_, 0);
lean_dec(v_unused_664_);
v___x_653_ = v___x_616_;
v_isShared_654_ = v_isSharedCheck_663_;
goto v_resetjp_652_;
}
else
{
lean_dec(v___x_616_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_663_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1));
lean_inc(v_a_609_);
v___x_656_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_609_, v___x_606_);
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
lean_dec_ref(v___x_656_);
v___x_658_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 0);
lean_ctor_set(v___x_653_, 0, v___x_659_);
v___x_661_ = v___x_653_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
lean_dec(v___x_616_);
lean_dec(v_val_611_);
lean_dec_ref(v_b_605_);
v___x_665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_609_);
v___x_666_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_609_, v___x_606_);
v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
lean_dec_ref(v___x_666_);
v___x_668_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_669_ = lean_string_append(v___x_667_, v___x_668_);
if (v_isShared_614_ == 0)
{
lean_ctor_set_tag(v___x_613_, 0);
lean_ctor_set(v___x_613_, 0, v___x_669_);
v___x_671_ = v___x_613_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v___x_610_);
lean_dec_ref(v_b_605_);
v___x_674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_609_);
v___x_675_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_609_, v___x_606_);
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
lean_dec_ref(v___x_675_);
v___x_677_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_678_ = lean_string_append(v___x_676_, v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___boxed(lean_object* v_challenge_680_, lean_object* v_solution_681_, lean_object* v_as_682_, lean_object* v_sz_683_, lean_object* v_i_684_, lean_object* v_b_685_){
_start:
{
size_t v_sz_boxed_686_; size_t v_i_boxed_687_; lean_object* v_res_688_; 
v_sz_boxed_686_ = lean_unbox_usize(v_sz_683_);
lean_dec(v_sz_683_);
v_i_boxed_687_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_680_, v_solution_681_, v_as_682_, v_sz_boxed_686_, v_i_boxed_687_, v_b_685_);
lean_dec_ref(v_as_682_);
lean_dec_ref(v_solution_681_);
lean_dec_ref(v_challenge_680_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(lean_object* v_challenge_691_, lean_object* v_solution_692_, lean_object* v_as_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_b_696_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v_b_696_);
return v___x_698_;
}
else
{
lean_object* v_constMap_699_; lean_object* v_a_700_; lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_724_; 
v_constMap_699_ = lean_ctor_get(v_challenge_691_, 0);
v_a_700_ = lean_array_uget_borrowed(v_as_693_, v_i_695_);
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_699_, v_a_700_);
if (lean_obj_tag(v___x_724_) == 1)
{
lean_object* v_val_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_749_; 
v_val_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_749_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_749_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_val_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_749_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_constMap_729_; lean_object* v___x_730_; 
v_constMap_729_ = lean_ctor_get(v_solution_692_, 0);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_729_, v_a_700_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_del_object(v___x_727_);
switch(lean_obj_tag(v_val_725_))
{
case 2:
{
lean_object* v_val_731_; 
v_val_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v___x_730_, 1);
if (lean_obj_tag(v_val_731_) == 2)
{
lean_object* v_val_732_; lean_object* v_val_733_; lean_object* v_toConstantVal_734_; lean_object* v_toConstantVal_735_; 
v_val_732_ = lean_ctor_get(v_val_725_, 0);
lean_inc_ref(v_val_732_);
lean_dec_ref_known(v_val_725_, 1);
v_val_733_ = lean_ctor_get(v_val_731_, 0);
lean_inc_ref(v_val_733_);
lean_dec_ref_known(v_val_731_, 1);
v_toConstantVal_734_ = lean_ctor_get(v_val_732_, 0);
lean_inc_ref(v_toConstantVal_734_);
lean_dec_ref(v_val_732_);
v_toConstantVal_735_ = lean_ctor_get(v_val_733_, 0);
lean_inc_ref(v_toConstantVal_735_);
lean_dec_ref(v_val_733_);
v_fst_709_ = v_toConstantVal_734_;
v_snd_710_ = v_toConstantVal_735_;
goto v___jp_708_;
}
else
{
lean_dec_ref_known(v_val_725_, 1);
lean_dec(v_val_731_);
lean_dec_ref(v_b_696_);
goto v___jp_701_;
}
}
case 0:
{
lean_object* v_val_736_; 
v_val_736_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_730_, 1);
if (lean_obj_tag(v_val_736_) == 0)
{
lean_object* v_val_737_; lean_object* v_val_738_; lean_object* v_toConstantVal_739_; lean_object* v_toConstantVal_740_; 
v_val_737_ = lean_ctor_get(v_val_725_, 0);
lean_inc_ref(v_val_737_);
lean_dec_ref_known(v_val_725_, 1);
v_val_738_ = lean_ctor_get(v_val_736_, 0);
lean_inc_ref(v_val_738_);
lean_dec_ref_known(v_val_736_, 1);
v_toConstantVal_739_ = lean_ctor_get(v_val_737_, 0);
lean_inc_ref(v_toConstantVal_739_);
lean_dec_ref(v_val_737_);
v_toConstantVal_740_ = lean_ctor_get(v_val_738_, 0);
lean_inc_ref(v_toConstantVal_740_);
lean_dec_ref(v_val_738_);
v_fst_709_ = v_toConstantVal_739_;
v_snd_710_ = v_toConstantVal_740_;
goto v___jp_708_;
}
else
{
lean_dec(v_val_736_);
lean_dec_ref_known(v_val_725_, 1);
lean_dec_ref(v_b_696_);
goto v___jp_701_;
}
}
default: 
{
lean_dec_ref_known(v___x_730_, 1);
lean_dec(v_val_725_);
lean_dec_ref(v_b_696_);
goto v___jp_701_;
}
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
lean_dec(v___x_730_);
lean_dec(v_val_725_);
lean_dec_ref(v_b_696_);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_700_);
v___x_742_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_700_, v___x_697_);
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
lean_dec_ref(v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
lean_ctor_set(v___x_727_, 0, v___x_745_);
v___x_747_ = v___x_727_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v___x_724_);
lean_dec_ref(v_b_696_);
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_700_);
v___x_751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_700_, v___x_697_);
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
lean_dec_ref(v___x_751_);
v___x_753_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
v___jp_701_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0));
lean_inc(v_a_700_);
v___x_703_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_700_, v___x_697_);
v___x_704_ = lean_string_append(v___x_702_, v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
v___jp_708_:
{
uint8_t v___x_711_; 
v___x_711_ = l_Lean_instBEqConstantVal_beq(v_fst_709_, v_snd_710_);
lean_dec_ref(v_snd_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec_ref(v_fst_709_);
lean_dec_ref(v_b_696_);
v___x_712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1));
lean_inc(v_a_700_);
v___x_713_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_700_, v___x_697_);
v___x_714_ = lean_string_append(v___x_712_, v___x_713_);
lean_dec_ref(v___x_713_);
v___x_715_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_716_ = lean_string_append(v___x_714_, v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v_type_718_; lean_object* v___x_719_; lean_object* v___x_720_; size_t v___x_721_; size_t v___x_722_; 
v_type_718_ = lean_ctor_get(v_fst_709_, 2);
lean_inc_ref(v_type_718_);
lean_dec_ref(v_fst_709_);
v___x_719_ = l_Lean_Expr_getUsedConstants(v_type_718_);
v___x_720_ = l_Array_append___redArg(v_b_696_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_695_, v___x_721_);
v_i_695_ = v___x_722_;
v_b_696_ = v___x_720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___boxed(lean_object* v_challenge_756_, lean_object* v_solution_757_, lean_object* v_as_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_b_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_756_, v_solution_757_, v_as_758_, v_sz_boxed_762_, v_i_boxed_763_, v_b_761_);
lean_dec_ref(v_as_758_);
lean_dec_ref(v_solution_757_);
lean_dec_ref(v_challenge_756_);
return v_res_764_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__0(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
v___x_766_ = lean_unsigned_to_nat(16u);
v___x_767_ = lean_mk_array(v___x_766_, v___x_765_);
return v___x_767_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__1(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lake_Check_compareAt___closed__0, &l_Lake_Check_compareAt___closed__0_once, _init_l_Lake_Check_compareAt___closed__0);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt(lean_object* v_challenge_771_, lean_object* v_solution_772_, lean_object* v_theoremTargets_773_, lean_object* v_definitionTargets_774_, lean_object* v_primitive_775_){
_start:
{
size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_sz_776_ = lean_array_size(v_theoremTargets_773_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_771_, v_solution_772_, v_theoremTargets_773_, v_sz_776_, v___x_777_, v_primitive_775_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v_solution_772_);
lean_dec_ref(v_challenge_771_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; size_t v_sz_788_; lean_object* v___x_789_; 
v_a_787_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_778_, 1);
v_sz_788_ = lean_array_size(v_definitionTargets_774_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_771_, v_solution_772_, v_definitionTargets_774_, v_sz_788_, v___x_777_, v_a_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_solution_772_);
lean_dec_ref(v_challenge_771_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_a_798_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_789_, 1);
v___x_799_ = lean_obj_once(&l_Lake_Check_compareAt___closed__1, &l_Lake_Check_compareAt___closed__1_once, _init_l_Lake_Check_compareAt___closed__1);
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_799_, v_definitionTargets_774_);
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_799_, v_theoremTargets_773_);
v___x_802_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_802_, 0, v_challenge_771_);
lean_ctor_set(v___x_802_, 1, v_solution_772_);
lean_ctor_set(v___x_802_, 2, v___x_800_);
lean_ctor_set(v___x_802_, 3, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_a_798_);
lean_ctor_set(v___x_803_, 1, v___x_799_);
v___x_804_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v___x_802_, v___x_803_);
lean_dec_ref_known(v___x_802_, 4);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_a_813_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_821_ == 0)
{
v___x_815_ = v___x_804_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_804_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_fst_817_; lean_object* v___x_819_; 
v_fst_817_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_fst_817_);
lean_dec(v_a_813_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_fst_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_fst_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt___boxed(lean_object* v_challenge_822_, lean_object* v_solution_823_, lean_object* v_theoremTargets_824_, lean_object* v_definitionTargets_825_, lean_object* v_primitive_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lake_Check_compareAt(v_challenge_822_, v_solution_823_, v_theoremTargets_824_, v_definitionTargets_825_, v_primitive_826_);
lean_dec_ref(v_definitionTargets_825_);
lean_dec_ref(v_theoremTargets_824_);
return v_res_827_;
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
