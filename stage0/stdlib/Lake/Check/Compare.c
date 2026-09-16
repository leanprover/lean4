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
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_506_; 
lean_inc_ref(v_checked_409_);
lean_inc_ref(v_worklist_408_);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; 
v_unused_507_ = lean_ctor_get(v_a_407_, 1);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_a_407_, 0);
lean_dec(v_unused_508_);
v___x_414_ = v_a_407_;
v_isShared_415_ = v_isSharedCheck_506_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_a_407_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_506_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___y_421_; lean_object* v_worklist_422_; lean_object* v_checked_423_; lean_object* v___y_431_; lean_object* v___y_432_; lean_object* v___y_436_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_sub(v___x_410_, v___x_417_);
v___x_419_ = lean_array_get(v___x_416_, v_worklist_408_, v___x_418_);
lean_dec(v___x_418_);
v___x_439_ = lean_array_pop(v_worklist_408_);
lean_inc_ref(v_checked_409_);
lean_inc_ref(v___x_439_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_checked_409_);
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_checked_409_, v___x_419_);
if (v___x_441_ == 0)
{
lean_object* v_challenge_442_; lean_object* v_solution_443_; lean_object* v_definitionTargets_444_; lean_object* v_theoremTargets_445_; lean_object* v_constMap_446_; lean_object* v___x_447_; 
v_challenge_442_ = lean_ctor_get(v_a_406_, 0);
v_solution_443_ = lean_ctor_get(v_a_406_, 1);
v_definitionTargets_444_ = lean_ctor_get(v_a_406_, 2);
v_theoremTargets_445_ = lean_ctor_get(v_a_406_, 3);
v_constMap_446_ = lean_ctor_get(v_challenge_442_, 0);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_446_, v___x_419_);
if (lean_obj_tag(v___x_447_) == 1)
{
lean_object* v_val_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_497_; 
v_val_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_497_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_497_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_val_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_497_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_constMap_452_; lean_object* v___x_453_; 
v_constMap_452_ = lean_ctor_get(v_solution_443_, 0);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_452_, v___x_419_);
if (lean_obj_tag(v___x_453_) == 1)
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_487_; 
lean_del_object(v___x_450_);
v_val_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_487_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_487_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_487_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = l_Lean_ConstantInfo_name(v_val_454_);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_definitionTargets_444_, v___x_471_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_addWorklist_spec__0___redArg(v_theoremTargets_445_, v___x_471_);
lean_dec(v___x_471_);
if (v___x_473_ == 0)
{
uint8_t v___x_474_; 
lean_dec_ref(v___x_439_);
lean_dec_ref(v_checked_409_);
v___x_474_ = l_Lean_instBEqConstantInfo_beq(v_val_448_, v_val_454_);
lean_dec(v_val_448_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_val_454_);
lean_dec_ref_known(v___x_440_, 2);
lean_del_object(v___x_414_);
v___x_475_ = 1;
v___x_476_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
v___x_477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_419_, v___x_475_);
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
lean_dec_ref(v___x_477_);
v___x_479_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_480_ = lean_string_append(v___x_478_, v___x_479_);
if (v_isShared_457_ == 0)
{
lean_ctor_set_tag(v___x_456_, 0);
lean_ctor_set(v___x_456_, 0, v___x_480_);
v___x_482_ = v___x_456_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
else
{
lean_object* v___x_484_; 
lean_del_object(v___x_456_);
v___x_484_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_addRelevantConsts(v_val_454_, v_a_406_, v___x_440_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_dec(v___x_419_);
lean_del_object(v___x_414_);
return v___x_484_;
}
else
{
lean_object* v_a_485_; lean_object* v_snd_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v_snd_486_ = lean_ctor_get(v_a_485_, 1);
lean_inc(v_snd_486_);
lean_dec(v_a_485_);
v___y_431_ = v_a_406_;
v___y_432_ = v_snd_486_;
goto v___jp_430_;
}
}
}
else
{
lean_del_object(v___x_456_);
lean_dec(v_val_448_);
goto v___jp_458_;
}
}
else
{
lean_dec(v___x_471_);
lean_del_object(v___x_456_);
lean_dec(v_val_448_);
goto v___jp_458_;
}
v___jp_458_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_459_ = l_Lean_ConstantInfo_type(v_val_454_);
lean_dec(v_val_454_);
v___x_460_ = l_Lean_Expr_getUsedConstants(v___x_459_);
v___x_461_ = lean_array_get_size(v___x_460_);
v___x_462_ = lean_nat_dec_lt(v___x_411_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec_ref(v___x_460_);
lean_dec_ref_known(v___x_440_, 2);
v___y_421_ = v_a_406_;
v_worklist_422_ = v___x_439_;
v_checked_423_ = v_checked_409_;
goto v___jp_420_;
}
else
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_nat_dec_le(v___x_461_, v___x_461_);
if (v___x_464_ == 0)
{
if (v___x_462_ == 0)
{
lean_dec_ref(v___x_460_);
lean_dec_ref_known(v___x_440_, 2);
v___y_421_ = v_a_406_;
v_worklist_422_ = v___x_439_;
v_checked_423_ = v_checked_409_;
goto v___jp_420_;
}
else
{
size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
lean_dec_ref(v___x_439_);
lean_dec_ref(v_checked_409_);
v___x_465_ = ((size_t)0ULL);
v___x_466_ = lean_usize_of_nat(v___x_461_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_460_, v___x_465_, v___x_466_, v___x_463_, v___x_440_);
lean_dec_ref(v___x_460_);
v___y_436_ = v___x_467_;
goto v___jp_435_;
}
}
else
{
size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; 
lean_dec_ref(v___x_439_);
lean_dec_ref(v_checked_409_);
v___x_468_ = ((size_t)0ULL);
v___x_469_ = lean_usize_of_nat(v___x_461_);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v___x_460_, v___x_468_, v___x_469_, v___x_463_, v___x_440_);
lean_dec_ref(v___x_460_);
v___y_436_ = v___x_470_;
goto v___jp_435_;
}
}
}
}
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec(v___x_453_);
lean_dec(v_val_448_);
lean_dec_ref_known(v___x_440_, 2);
lean_dec_ref(v___x_439_);
lean_del_object(v___x_414_);
lean_dec_ref(v_checked_409_);
v___x_488_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__2));
v___x_489_ = 1;
v___x_490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_419_, v___x_489_);
v___x_491_ = lean_string_append(v___x_488_, v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
lean_ctor_set(v___x_450_, 0, v___x_493_);
v___x_495_ = v___x_450_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec(v___x_447_);
lean_dec_ref_known(v___x_440_, 2);
lean_dec_ref(v___x_439_);
lean_del_object(v___x_414_);
lean_dec_ref(v_checked_409_);
v___x_498_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__3));
v___x_499_ = 1;
v___x_500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_419_, v___x_499_);
v___x_501_ = lean_string_append(v___x_498_, v___x_500_);
lean_dec_ref(v___x_500_);
v___x_502_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
v___x_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
else
{
lean_dec_ref(v___x_439_);
lean_dec(v___x_419_);
lean_del_object(v___x_414_);
lean_dec_ref(v_checked_409_);
v_a_407_ = v___x_440_;
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
v___jp_435_:
{
if (lean_obj_tag(v___y_436_) == 0)
{
lean_dec(v___x_419_);
lean_del_object(v___x_414_);
return v___y_436_;
}
else
{
lean_object* v_a_437_; lean_object* v_snd_438_; 
v_a_437_ = lean_ctor_get(v___y_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___y_436_, 1);
v_snd_438_ = lean_ctor_get(v_a_437_, 1);
lean_inc(v_snd_438_);
lean_dec(v_a_437_);
v___y_431_ = v_a_406_;
v___y_432_ = v_snd_438_;
goto v___jp_430_;
}
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_a_407_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___boxed(lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v_a_512_, v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0(lean_object* v_00_u03b2_515_, lean_object* v_m_516_, lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_m_516_, v_a_517_, v_b_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(lean_object* v_00_u03b2_520_, lean_object* v_m_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_m_521_, v_a_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___boxed(lean_object* v_00_u03b2_524_, lean_object* v_m_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1(v_00_u03b2_524_, v_m_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_m_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(lean_object* v_as_528_, size_t v_i_529_, size_t v_stop_530_, lean_object* v_b_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___redArg(v_as_528_, v_i_529_, v_stop_530_, v_b_531_, v___y_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2___boxed(lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
size_t v_i_boxed_541_; size_t v_stop_boxed_542_; lean_object* v_res_543_; 
v_i_boxed_541_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_542_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__2(v_as_535_, v_i_boxed_541_, v_stop_boxed_542_, v_b_538_, v___y_539_, v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_as_535_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0(lean_object* v_00_u03b2_544_, lean_object* v_data_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0___redArg(v_data_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(lean_object* v_00_u03b2_547_, lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___redArg(v_a_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2___boxed(lean_object* v_00_u03b2_551_, lean_object* v_a_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1_spec__2(v_00_u03b2_551_, v_a_552_, v_x_553_);
lean_dec(v_x_553_);
lean_dec(v_a_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_555_, lean_object* v_i_556_, lean_object* v_source_557_, lean_object* v_target_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1___redArg(v_i_556_, v_source_557_, v_target_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0_spec__0_spec__1_spec__4___redArg(v_x_561_, v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT uint8_t l_Lake_Check_definitionHoleMatches(lean_object* v_challengeHole_564_, lean_object* v_solutionHole_565_){
_start:
{
lean_object* v_toConstantVal_566_; uint8_t v_safety_567_; lean_object* v_toConstantVal_568_; uint8_t v_safety_569_; uint8_t v___x_570_; 
v_toConstantVal_566_ = lean_ctor_get(v_challengeHole_564_, 0);
v_safety_567_ = lean_ctor_get_uint8(v_challengeHole_564_, sizeof(void*)*4);
v_toConstantVal_568_ = lean_ctor_get(v_solutionHole_565_, 0);
v_safety_569_ = lean_ctor_get_uint8(v_solutionHole_565_, sizeof(void*)*4);
v___x_570_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_566_, v_toConstantVal_568_);
if (v___x_570_ == 0)
{
return v___x_570_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_567_, v_safety_569_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_definitionHoleMatches___boxed(lean_object* v_challengeHole_572_, lean_object* v_solutionHole_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Lake_Check_definitionHoleMatches(v_challengeHole_572_, v_solutionHole_573_);
lean_dec_ref(v_solutionHole_573_);
lean_dec_ref(v_challengeHole_572_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_580_ == 0)
{
return v_b_579_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v_r_583_; size_t v___x_584_; size_t v___x_585_; 
v_a_581_ = lean_array_uget_borrowed(v_as_576_, v_i_578_);
v___x_582_ = lean_box(0);
lean_inc(v_a_581_);
v_r_583_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__0___redArg(v_b_579_, v_a_581_, v___x_582_);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_578_, v___x_584_);
v_i_578_ = v___x_585_;
v_b_579_ = v_r_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2___boxed(lean_object* v_as_587_, lean_object* v_sz_588_, lean_object* v_i_589_, lean_object* v_b_590_){
_start:
{
size_t v_sz_boxed_591_; size_t v_i_boxed_592_; lean_object* v_res_593_; 
v_sz_boxed_591_ = lean_unbox_usize(v_sz_588_);
lean_dec(v_sz_588_);
v_i_boxed_592_ = lean_unbox_usize(v_i_589_);
lean_dec(v_i_589_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_as_587_, v_sz_boxed_591_, v_i_boxed_592_, v_b_590_);
lean_dec_ref(v_as_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(lean_object* v_m_594_, lean_object* v_l_595_){
_start:
{
size_t v_sz_596_; size_t v___x_597_; lean_object* v___x_598_; 
v_sz_596_ = lean_array_size(v_l_595_);
v___x_597_ = ((size_t)0ULL);
v___x_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2_spec__2(v_l_595_, v_sz_596_, v___x_597_, v_m_594_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2___boxed(lean_object* v_m_599_, lean_object* v_l_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v_m_599_, v_l_600_);
lean_dec_ref(v_l_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(lean_object* v_challenge_606_, lean_object* v_solution_607_, lean_object* v_as_608_, size_t v_sz_609_, size_t v_i_610_, lean_object* v_b_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = lean_usize_dec_lt(v_i_610_, v_sz_609_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_b_611_);
return v___x_613_;
}
else
{
lean_object* v_constMap_614_; lean_object* v_a_615_; lean_object* v___x_616_; 
v_constMap_614_ = lean_ctor_get(v_challenge_606_, 0);
v_a_615_ = lean_array_uget_borrowed(v_as_608_, v_i_610_);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_614_, v_a_615_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_679_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_679_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_679_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_679_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_constMap_621_; lean_object* v___x_622_; 
v_constMap_621_ = lean_ctor_get(v_solution_607_, 0);
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_621_, v_a_615_);
if (lean_obj_tag(v___x_622_) == 1)
{
lean_del_object(v___x_619_);
if (lean_obj_tag(v_val_617_) == 1)
{
lean_object* v_val_623_; 
v_val_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_623_);
lean_dec_ref_known(v___x_622_, 1);
if (lean_obj_tag(v_val_623_) == 1)
{
lean_object* v_val_624_; lean_object* v_val_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_644_; 
v_val_624_ = lean_ctor_get(v_val_617_, 0);
lean_inc_ref(v_val_624_);
lean_dec_ref_known(v_val_617_, 1);
v_val_625_ = lean_ctor_get(v_val_623_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_val_623_);
if (v_isSharedCheck_644_ == 0)
{
v___x_627_ = v_val_623_;
v_isShared_628_ = v_isSharedCheck_644_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_val_625_);
lean_dec(v_val_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_644_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
uint8_t v___x_629_; 
v___x_629_ = l_Lake_Check_definitionHoleMatches(v_val_624_, v_val_625_);
lean_dec_ref(v_val_624_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec_ref(v_val_625_);
lean_dec_ref(v_b_611_);
v___x_630_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__0));
lean_inc(v_a_615_);
v___x_631_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_615_, v___x_612_);
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 0);
lean_ctor_set(v___x_627_, 0, v___x_634_);
v___x_636_ = v___x_627_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v_toConstantVal_638_; lean_object* v_name_639_; lean_object* v___x_640_; size_t v___x_641_; size_t v___x_642_; 
lean_del_object(v___x_627_);
v_toConstantVal_638_ = lean_ctor_get(v_val_625_, 0);
lean_inc_ref(v_toConstantVal_638_);
lean_dec_ref(v_val_625_);
v_name_639_ = lean_ctor_get(v_toConstantVal_638_, 0);
lean_inc(v_name_639_);
lean_dec_ref(v_toConstantVal_638_);
v___x_640_ = lean_array_push(v_b_611_, v_name_639_);
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_i_610_, v___x_641_);
v_i_610_ = v___x_642_;
v_b_611_ = v___x_640_;
goto _start;
}
}
}
else
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_val_623_);
lean_dec_ref(v_b_611_);
v_isSharedCheck_656_ = !lean_is_exclusive(v_val_617_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_val_617_, 0);
lean_dec(v_unused_657_);
v___x_646_ = v_val_617_;
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
else
{
lean_dec(v_val_617_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_656_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__0));
lean_inc(v_a_615_);
v___x_649_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_615_, v___x_612_);
v___x_650_ = lean_string_append(v___x_648_, v___x_649_);
lean_dec_ref(v___x_649_);
v___x_651_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_652_ = lean_string_append(v___x_650_, v___x_651_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 0);
lean_ctor_set(v___x_646_, 0, v___x_652_);
v___x_654_ = v___x_646_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_val_617_);
lean_dec_ref(v_b_611_);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_622_, 0);
lean_dec(v_unused_670_);
v___x_659_ = v___x_622_;
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
else
{
lean_dec(v___x_622_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_669_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__1));
lean_inc(v_a_615_);
v___x_662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_615_, v___x_612_);
v___x_663_ = lean_string_append(v___x_661_, v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_665_ = lean_string_append(v___x_663_, v___x_664_);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 0);
lean_ctor_set(v___x_659_, 0, v___x_665_);
v___x_667_ = v___x_659_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_dec(v___x_622_);
lean_dec(v_val_617_);
lean_dec_ref(v_b_611_);
v___x_671_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_615_);
v___x_672_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_615_, v___x_612_);
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_675_ = lean_string_append(v___x_673_, v___x_674_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 0);
lean_ctor_set(v___x_619_, 0, v___x_675_);
v___x_677_ = v___x_619_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_dec(v___x_616_);
lean_dec_ref(v_b_611_);
v___x_680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_615_);
v___x_681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_615_, v___x_612_);
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
lean_dec_ref(v___x_681_);
v___x_683_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_684_ = lean_string_append(v___x_682_, v___x_683_);
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___boxed(lean_object* v_challenge_686_, lean_object* v_solution_687_, lean_object* v_as_688_, lean_object* v_sz_689_, lean_object* v_i_690_, lean_object* v_b_691_){
_start:
{
size_t v_sz_boxed_692_; size_t v_i_boxed_693_; lean_object* v_res_694_; 
v_sz_boxed_692_ = lean_unbox_usize(v_sz_689_);
lean_dec(v_sz_689_);
v_i_boxed_693_ = lean_unbox_usize(v_i_690_);
lean_dec(v_i_690_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_686_, v_solution_687_, v_as_688_, v_sz_boxed_692_, v_i_boxed_693_, v_b_691_);
lean_dec_ref(v_as_688_);
lean_dec_ref(v_solution_687_);
lean_dec_ref(v_challenge_686_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(lean_object* v_challenge_697_, lean_object* v_solution_698_, lean_object* v_as_699_, size_t v_sz_700_, size_t v_i_701_, lean_object* v_b_702_){
_start:
{
uint8_t v___x_703_; 
v___x_703_ = lean_usize_dec_lt(v_i_701_, v_sz_700_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v_b_702_);
return v___x_704_;
}
else
{
lean_object* v_constMap_705_; lean_object* v_a_706_; lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_730_; 
v_constMap_705_ = lean_ctor_get(v_challenge_697_, 0);
v_a_706_ = lean_array_uget_borrowed(v_as_699_, v_i_701_);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_705_, v_a_706_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_755_; 
v_val_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_755_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_755_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_755_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_constMap_735_; lean_object* v___x_736_; 
v_constMap_735_ = lean_ctor_get(v_solution_698_, 0);
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Compare_0__Lake_Check_Compare_loop_spec__1___redArg(v_constMap_735_, v_a_706_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_del_object(v___x_733_);
switch(lean_obj_tag(v_val_731_))
{
case 2:
{
lean_object* v_val_737_; 
v_val_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_736_, 1);
if (lean_obj_tag(v_val_737_) == 2)
{
lean_object* v_val_738_; lean_object* v_val_739_; lean_object* v_toConstantVal_740_; lean_object* v_toConstantVal_741_; 
v_val_738_ = lean_ctor_get(v_val_731_, 0);
lean_inc_ref(v_val_738_);
lean_dec_ref_known(v_val_731_, 1);
v_val_739_ = lean_ctor_get(v_val_737_, 0);
lean_inc_ref(v_val_739_);
lean_dec_ref_known(v_val_737_, 1);
v_toConstantVal_740_ = lean_ctor_get(v_val_738_, 0);
lean_inc_ref(v_toConstantVal_740_);
lean_dec_ref(v_val_738_);
v_toConstantVal_741_ = lean_ctor_get(v_val_739_, 0);
lean_inc_ref(v_toConstantVal_741_);
lean_dec_ref(v_val_739_);
v_fst_715_ = v_toConstantVal_740_;
v_snd_716_ = v_toConstantVal_741_;
goto v___jp_714_;
}
else
{
lean_dec_ref_known(v_val_731_, 1);
lean_dec(v_val_737_);
lean_dec_ref(v_b_702_);
goto v___jp_707_;
}
}
case 0:
{
lean_object* v_val_742_; 
v_val_742_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_736_, 1);
if (lean_obj_tag(v_val_742_) == 0)
{
lean_object* v_val_743_; lean_object* v_val_744_; lean_object* v_toConstantVal_745_; lean_object* v_toConstantVal_746_; 
v_val_743_ = lean_ctor_get(v_val_731_, 0);
lean_inc_ref(v_val_743_);
lean_dec_ref_known(v_val_731_, 1);
v_val_744_ = lean_ctor_get(v_val_742_, 0);
lean_inc_ref(v_val_744_);
lean_dec_ref_known(v_val_742_, 1);
v_toConstantVal_745_ = lean_ctor_get(v_val_743_, 0);
lean_inc_ref(v_toConstantVal_745_);
lean_dec_ref(v_val_743_);
v_toConstantVal_746_ = lean_ctor_get(v_val_744_, 0);
lean_inc_ref(v_toConstantVal_746_);
lean_dec_ref(v_val_744_);
v_fst_715_ = v_toConstantVal_745_;
v_snd_716_ = v_toConstantVal_746_;
goto v___jp_714_;
}
else
{
lean_dec(v_val_742_);
lean_dec_ref_known(v_val_731_, 1);
lean_dec_ref(v_b_702_);
goto v___jp_707_;
}
}
default: 
{
lean_dec_ref_known(v___x_736_, 1);
lean_dec(v_val_731_);
lean_dec_ref(v_b_702_);
goto v___jp_707_;
}
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec(v___x_736_);
lean_dec(v_val_731_);
lean_dec_ref(v_b_702_);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__2));
lean_inc(v_a_706_);
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_706_, v___x_703_);
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
lean_dec_ref(v___x_748_);
v___x_750_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 0);
lean_ctor_set(v___x_733_, 0, v___x_751_);
v___x_753_ = v___x_733_;
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
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v___x_730_);
lean_dec_ref(v_b_702_);
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1___closed__3));
lean_inc(v_a_706_);
v___x_757_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_706_, v___x_703_);
v___x_758_ = lean_string_append(v___x_756_, v___x_757_);
lean_dec_ref(v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_760_ = lean_string_append(v___x_758_, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__0));
lean_inc(v_a_706_);
v___x_709_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_706_, v___x_703_);
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
lean_dec_ref(v___x_709_);
v___x_711_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_712_ = lean_string_append(v___x_710_, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
v___jp_714_:
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_instBEqConstantVal_beq(v_fst_715_, v_snd_716_);
lean_dec_ref(v_snd_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec_ref(v_fst_715_);
lean_dec_ref(v_b_702_);
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___closed__1));
lean_inc(v_a_706_);
v___x_719_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_706_, v___x_703_);
v___x_720_ = lean_string_append(v___x_718_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop___closed__1));
v___x_722_ = lean_string_append(v___x_720_, v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
else
{
lean_object* v_type_724_; lean_object* v___x_725_; lean_object* v___x_726_; size_t v___x_727_; size_t v___x_728_; 
v_type_724_ = lean_ctor_get(v_fst_715_, 2);
lean_inc_ref(v_type_724_);
lean_dec_ref(v_fst_715_);
v___x_725_ = l_Lean_Expr_getUsedConstants(v_type_724_);
v___x_726_ = l_Array_append___redArg(v_b_702_, v___x_725_);
lean_dec_ref(v___x_725_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_701_, v___x_727_);
v_i_701_ = v___x_728_;
v_b_702_ = v___x_726_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0___boxed(lean_object* v_challenge_762_, lean_object* v_solution_763_, lean_object* v_as_764_, lean_object* v_sz_765_, lean_object* v_i_766_, lean_object* v_b_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_769_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_762_, v_solution_763_, v_as_764_, v_sz_boxed_768_, v_i_boxed_769_, v_b_767_);
lean_dec_ref(v_as_764_);
lean_dec_ref(v_solution_763_);
lean_dec_ref(v_challenge_762_);
return v_res_770_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__0(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_box(0);
v___x_772_ = lean_unsigned_to_nat(16u);
v___x_773_ = lean_mk_array(v___x_772_, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l_Lake_Check_compareAt___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l_Lake_Check_compareAt___closed__0, &l_Lake_Check_compareAt___closed__0_once, _init_l_Lake_Check_compareAt___closed__0);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v___x_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt(lean_object* v_challenge_777_, lean_object* v_solution_778_, lean_object* v_theoremTargets_779_, lean_object* v_definitionTargets_780_, lean_object* v_primitive_781_){
_start:
{
size_t v_sz_782_; size_t v___x_783_; lean_object* v___x_784_; 
v_sz_782_ = lean_array_size(v_theoremTargets_779_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__0(v_challenge_777_, v_solution_778_, v_theoremTargets_779_, v_sz_782_, v___x_783_, v_primitive_781_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_solution_778_);
lean_dec_ref(v_challenge_777_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; size_t v_sz_794_; lean_object* v___x_795_; 
v_a_793_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_784_, 1);
v_sz_794_ = lean_array_size(v_definitionTargets_780_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_compareAt_spec__1(v_challenge_777_, v_solution_778_, v_definitionTargets_780_, v_sz_794_, v___x_783_, v_a_793_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_solution_778_);
lean_dec_ref(v_challenge_777_);
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
lean_object* v_a_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_a_804_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_795_, 1);
v___x_805_ = lean_obj_once(&l_Lake_Check_compareAt___closed__1, &l_Lake_Check_compareAt___closed__1_once, _init_l_Lake_Check_compareAt___closed__1);
v___x_806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_805_, v_definitionTargets_780_);
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_compareAt_spec__2(v___x_805_, v_theoremTargets_779_);
v___x_808_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_808_, 0, v_challenge_777_);
lean_ctor_set(v___x_808_, 1, v_solution_778_);
lean_ctor_set(v___x_808_, 2, v___x_806_);
lean_ctor_set(v___x_808_, 3, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v_a_804_);
lean_ctor_set(v___x_809_, 1, v___x_805_);
v___x_810_ = l___private_Lake_Check_Compare_0__Lake_Check_Compare_loop(v___x_808_, v___x_809_);
lean_dec_ref_known(v___x_808_, 4);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_819_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_810_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_810_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v_fst_823_; lean_object* v___x_825_; 
v_fst_823_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_fst_823_);
lean_dec(v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_fst_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_compareAt___boxed(lean_object* v_challenge_828_, lean_object* v_solution_829_, lean_object* v_theoremTargets_830_, lean_object* v_definitionTargets_831_, lean_object* v_primitive_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lake_Check_compareAt(v_challenge_828_, v_solution_829_, v_theoremTargets_830_, v_definitionTargets_831_, v_primitive_832_);
lean_dec_ref(v_definitionTargets_831_);
lean_dec_ref(v_theoremTargets_830_);
return v_res_833_;
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
