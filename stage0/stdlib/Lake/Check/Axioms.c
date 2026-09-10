// Lean compiler output
// Module: Lake.Check.Axioms
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
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Illegal axiom detected: '"};
static const lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__0 = (const lean_object*)&l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__0_value;
static const lean_string_object l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1 = (const lean_object*)&l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1_value;
static const lean_string_object l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Constant not found in solution '"};
static const lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2 = (const lean_object*)&l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___closed__0 = (const lean_object*)&l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___closed__0_value;
static const lean_ctor_object l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1 = (const lean_object*)&l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___closed__0 = (const lean_object*)&l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___closed__0 = (const lean_object*)&l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Check_usedAxioms___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_usedAxioms___closed__0;
static lean_once_cell_t l_Lake_Check_usedAxioms___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_usedAxioms___closed__1;
static const lean_array_object l_Lake_Check_usedAxioms___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Check_usedAxioms___closed__2 = (const lean_object*)&l_Lake_Check_usedAxioms___closed__2_value;
static lean_once_cell_t l_Lake_Check_usedAxioms___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_usedAxioms___closed__3;
LEAN_EXPORT lean_object* l_Lake_Check_usedAxioms(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Solution constant is not a theorem: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Const not found in solution: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Solution constant is not a definition: '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Check_checkAxioms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Check_checkAxioms___closed__0 = (const lean_object*)&l_Lake_Check_checkAxioms___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_value_5_; lean_object* v_tail_6_; uint8_t v___x_7_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_value_5_ = lean_ctor_get(v_x_2_, 1);
v_tail_6_ = lean_ctor_get(v_x_2_, 2);
v___x_7_ = lean_name_eq(v_key_4_, v_a_1_);
if (v___x_7_ == 0)
{
v_x_2_ = v_tail_6_;
goto _start;
}
else
{
lean_object* v___x_9_; 
lean_inc(v_value_5_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_value_5_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
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
uint64_t v___x_19_; uint64_t v___x_20_; uint64_t v_fold_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; size_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
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
v___x_31_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg(v_a_14_, v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg___boxed(lean_object* v_m_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_m_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_m_34_);
return v_res_36_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(lean_object* v_a_37_, lean_object* v_x_38_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
uint8_t v___x_39_; 
v___x_39_ = 0;
return v___x_39_;
}
else
{
lean_object* v_key_40_; lean_object* v_tail_41_; uint8_t v___x_42_; 
v_key_40_ = lean_ctor_get(v_x_38_, 0);
v_tail_41_ = lean_ctor_get(v_x_38_, 2);
v___x_42_ = lean_name_eq(v_key_40_, v_a_37_);
if (v___x_42_ == 0)
{
v_x_38_ = v_tail_41_;
goto _start;
}
else
{
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg___boxed(lean_object* v_a_44_, lean_object* v_x_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_44_, v_x_45_);
lean_dec(v_x_45_);
lean_dec(v_a_44_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(lean_object* v_m_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_buckets_50_; lean_object* v___x_51_; uint64_t v___y_53_; 
v_buckets_50_ = lean_ctor_get(v_m_48_, 1);
v___x_51_ = lean_array_get_size(v_buckets_50_);
if (lean_obj_tag(v_a_49_) == 0)
{
uint64_t v___x_67_; 
v___x_67_ = 1723ULL;
v___y_53_ = v___x_67_;
goto v___jp_52_;
}
else
{
uint64_t v_hash_68_; 
v_hash_68_ = lean_ctor_get_uint64(v_a_49_, sizeof(void*)*2);
v___y_53_ = v_hash_68_;
goto v___jp_52_;
}
v___jp_52_:
{
uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v_fold_56_; uint64_t v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_54_ = 32ULL;
v___x_55_ = lean_uint64_shift_right(v___y_53_, v___x_54_);
v_fold_56_ = lean_uint64_xor(v___y_53_, v___x_55_);
v___x_57_ = 16ULL;
v___x_58_ = lean_uint64_shift_right(v_fold_56_, v___x_57_);
v___x_59_ = lean_uint64_xor(v_fold_56_, v___x_58_);
v___x_60_ = lean_uint64_to_usize(v___x_59_);
v___x_61_ = lean_usize_of_nat(v___x_51_);
v___x_62_ = ((size_t)1ULL);
v___x_63_ = lean_usize_sub(v___x_61_, v___x_62_);
v___x_64_ = lean_usize_land(v___x_60_, v___x_63_);
v___x_65_ = lean_array_uget_borrowed(v_buckets_50_, v___x_64_);
v___x_66_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_49_, v___x_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg___boxed(lean_object* v_m_69_, lean_object* v_a_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_m_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_m_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst(lean_object* v_n_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___y_80_; lean_object* v_solution_100_; lean_object* v_legalAxioms_101_; lean_object* v_constMap_102_; lean_object* v___x_103_; 
v_solution_100_ = lean_ctor_get(v_a_77_, 0);
v_legalAxioms_101_ = lean_ctor_get(v_a_77_, 1);
v_constMap_102_ = lean_ctor_get(v_solution_100_, 0);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_102_, v_n_76_);
if (lean_obj_tag(v___x_103_) == 1)
{
lean_object* v_val_104_; 
v_val_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v___x_103_, 1);
if (lean_obj_tag(v_val_104_) == 0)
{
lean_object* v_val_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_121_; 
v_val_105_ = lean_ctor_get(v_val_104_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v_val_104_);
if (v_isSharedCheck_121_ == 0)
{
v___x_107_ = v_val_104_;
v_isShared_108_ = v_isSharedCheck_121_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_val_105_);
lean_dec(v_val_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_121_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_toConstantVal_109_; lean_object* v_name_110_; uint8_t v___x_111_; 
v_toConstantVal_109_ = lean_ctor_get(v_val_105_, 0);
lean_inc_ref(v_toConstantVal_109_);
lean_dec_ref(v_val_105_);
v_name_110_ = lean_ctor_get(v_toConstantVal_109_, 0);
lean_inc(v_name_110_);
lean_dec_ref(v_toConstantVal_109_);
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_legalAxioms_101_, v_name_110_);
lean_dec(v_name_110_);
if (v___x_111_ == 0)
{
uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
lean_dec_ref(v_a_78_);
v___x_112_ = 1;
v___x_113_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__0));
v___x_114_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_76_, v___x_112_);
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
lean_dec_ref(v___x_114_);
v___x_116_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_117_);
v___x_119_ = v___x_107_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
else
{
lean_del_object(v___x_107_);
v___y_80_ = v_a_78_;
goto v___jp_79_;
}
}
}
else
{
lean_dec(v_val_104_);
v___y_80_ = v_a_78_;
goto v___jp_79_;
}
}
else
{
lean_object* v___x_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v___x_103_);
lean_dec_ref(v_a_78_);
v___x_122_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2));
v___x_123_ = 1;
v___x_124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_76_, v___x_123_);
v___x_125_ = lean_string_append(v___x_122_, v___x_124_);
lean_dec_ref(v___x_124_);
v___x_126_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_127_ = lean_string_append(v___x_125_, v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
v___jp_79_:
{
lean_object* v_worklist_81_; lean_object* v_checked_82_; uint8_t v___x_83_; 
v_worklist_81_ = lean_ctor_get(v___y_80_, 0);
v_checked_82_ = lean_ctor_get(v___y_80_, 1);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_checked_82_, v_n_76_);
if (v___x_83_ == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_94_; 
lean_inc_ref(v_checked_82_);
lean_inc_ref(v_worklist_81_);
v_isSharedCheck_94_ = !lean_is_exclusive(v___y_80_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; 
v_unused_95_ = lean_ctor_get(v___y_80_, 1);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v___y_80_, 0);
lean_dec(v_unused_96_);
v___x_85_ = v___y_80_;
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
else
{
lean_dec(v___y_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_array_push(v_worklist_81_, v_n_76_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_88_);
v___x_90_ = v___x_85_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_checked_82_);
v___x_90_ = v_reuseFailAlloc_93_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
return v___x_92_;
}
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_dec(v_n_76_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___y_80_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___boxed(lean_object* v_n_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst(v_n_129_, v_a_130_, v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_132_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0(lean_object* v_00_u03b2_133_, lean_object* v_m_134_, lean_object* v_a_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_m_134_, v_a_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___boxed(lean_object* v_00_u03b2_137_, lean_object* v_m_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0(v_00_u03b2_137_, v_m_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_m_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1(lean_object* v_00_u03b2_142_, lean_object* v_m_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_m_143_, v_a_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___boxed(lean_object* v_00_u03b2_146_, lean_object* v_m_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1(v_00_u03b2_146_, v_m_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_m_147_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0(lean_object* v_00_u03b2_150_, lean_object* v_a_151_, lean_object* v_x_152_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_151_, v_x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_154_, lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0(v_00_u03b2_154_, v_a_155_, v_x_156_);
lean_dec(v_x_156_);
lean_dec(v_a_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2(lean_object* v_00_u03b2_159_, lean_object* v_a_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg(v_a_160_, v_x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___boxed(lean_object* v_00_u03b2_163_, lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2(v_00_u03b2_163_, v_a_164_, v_x_165_);
lean_dec(v_x_165_);
lean_dec(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
return v_x_167_;
}
else
{
lean_object* v_key_169_; lean_object* v_value_170_; lean_object* v_tail_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_197_; 
v_key_169_ = lean_ctor_get(v_x_168_, 0);
v_value_170_ = lean_ctor_get(v_x_168_, 1);
v_tail_171_ = lean_ctor_get(v_x_168_, 2);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_197_ == 0)
{
v___x_173_ = v_x_168_;
v_isShared_174_ = v_isSharedCheck_197_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_tail_171_);
lean_inc(v_value_170_);
lean_inc(v_key_169_);
lean_dec(v_x_168_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_197_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; uint64_t v___y_177_; 
v___x_175_ = lean_array_get_size(v_x_167_);
if (lean_obj_tag(v_key_169_) == 0)
{
uint64_t v___x_195_; 
v___x_195_ = 1723ULL;
v___y_177_ = v___x_195_;
goto v___jp_176_;
}
else
{
uint64_t v_hash_196_; 
v_hash_196_ = lean_ctor_get_uint64(v_key_169_, sizeof(void*)*2);
v___y_177_ = v_hash_196_;
goto v___jp_176_;
}
v___jp_176_:
{
uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v_fold_180_; uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_178_ = 32ULL;
v___x_179_ = lean_uint64_shift_right(v___y_177_, v___x_178_);
v_fold_180_ = lean_uint64_xor(v___y_177_, v___x_179_);
v___x_181_ = 16ULL;
v___x_182_ = lean_uint64_shift_right(v_fold_180_, v___x_181_);
v___x_183_ = lean_uint64_xor(v_fold_180_, v___x_182_);
v___x_184_ = lean_uint64_to_usize(v___x_183_);
v___x_185_ = lean_usize_of_nat(v___x_175_);
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_sub(v___x_185_, v___x_186_);
v___x_188_ = lean_usize_land(v___x_184_, v___x_187_);
v___x_189_ = lean_array_uget_borrowed(v_x_167_, v___x_188_);
lean_inc(v___x_189_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 2, v___x_189_);
v___x_191_ = v___x_173_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_key_169_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_value_170_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v___x_189_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; 
v___x_192_ = lean_array_uset(v_x_167_, v___x_188_, v___x_191_);
v_x_167_ = v___x_192_;
v_x_168_ = v_tail_171_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(lean_object* v_i_198_, lean_object* v_source_199_, lean_object* v_target_200_){
_start:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_array_get_size(v_source_199_);
v___x_202_ = lean_nat_dec_lt(v_i_198_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec_ref(v_source_199_);
lean_dec(v_i_198_);
return v_target_200_;
}
else
{
lean_object* v_es_203_; lean_object* v___x_204_; lean_object* v_source_205_; lean_object* v_target_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_es_203_ = lean_array_fget(v_source_199_, v_i_198_);
v___x_204_ = lean_box(0);
v_source_205_ = lean_array_fset(v_source_199_, v_i_198_, v___x_204_);
v_target_206_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(v_target_200_, v_es_203_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_i_198_, v___x_207_);
lean_dec(v_i_198_);
v_i_198_ = v___x_208_;
v_source_199_ = v_source_205_;
v_target_200_ = v_target_206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(lean_object* v_data_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_nbuckets_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_211_ = lean_array_get_size(v_data_210_);
v___x_212_ = lean_unsigned_to_nat(2u);
v_nbuckets_213_ = lean_nat_mul(v___x_211_, v___x_212_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_box(0);
v___x_216_ = lean_mk_array(v_nbuckets_213_, v___x_215_);
v___x_217_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(v___x_214_, v_data_210_, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(lean_object* v_m_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v_size_221_; lean_object* v_buckets_222_; lean_object* v___x_223_; uint64_t v___y_225_; 
v_size_221_ = lean_ctor_get(v_m_218_, 0);
v_buckets_222_ = lean_ctor_get(v_m_218_, 1);
v___x_223_ = lean_array_get_size(v_buckets_222_);
if (lean_obj_tag(v_a_219_) == 0)
{
uint64_t v___x_262_; 
v___x_262_ = 1723ULL;
v___y_225_ = v___x_262_;
goto v___jp_224_;
}
else
{
uint64_t v_hash_263_; 
v_hash_263_ = lean_ctor_get_uint64(v_a_219_, sizeof(void*)*2);
v___y_225_ = v_hash_263_;
goto v___jp_224_;
}
v___jp_224_:
{
uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v_fold_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; lean_object* v_bkt_237_; uint8_t v___x_238_; 
v___x_226_ = 32ULL;
v___x_227_ = lean_uint64_shift_right(v___y_225_, v___x_226_);
v_fold_228_ = lean_uint64_xor(v___y_225_, v___x_227_);
v___x_229_ = 16ULL;
v___x_230_ = lean_uint64_shift_right(v_fold_228_, v___x_229_);
v___x_231_ = lean_uint64_xor(v_fold_228_, v___x_230_);
v___x_232_ = lean_uint64_to_usize(v___x_231_);
v___x_233_ = lean_usize_of_nat(v___x_223_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_sub(v___x_233_, v___x_234_);
v___x_236_ = lean_usize_land(v___x_232_, v___x_235_);
v_bkt_237_ = lean_array_uget_borrowed(v_buckets_222_, v___x_236_);
v___x_238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_219_, v_bkt_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_259_; 
lean_inc_ref(v_buckets_222_);
lean_inc(v_size_221_);
v_isSharedCheck_259_ = !lean_is_exclusive(v_m_218_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; lean_object* v_unused_261_; 
v_unused_260_ = lean_ctor_get(v_m_218_, 1);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_m_218_, 0);
lean_dec(v_unused_261_);
v___x_240_ = v_m_218_;
v_isShared_241_ = v_isSharedCheck_259_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_m_218_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_259_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v_size_x27_243_; lean_object* v___x_244_; lean_object* v_buckets_x27_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v_size_x27_243_ = lean_nat_add(v_size_221_, v___x_242_);
lean_dec(v_size_221_);
lean_inc(v_bkt_237_);
v___x_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_244_, 0, v_a_219_);
lean_ctor_set(v___x_244_, 1, v_b_220_);
lean_ctor_set(v___x_244_, 2, v_bkt_237_);
v_buckets_x27_245_ = lean_array_uset(v_buckets_222_, v___x_236_, v___x_244_);
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_nat_mul(v_size_x27_243_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(3u);
v___x_249_ = lean_nat_div(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_array_get_size(v_buckets_x27_245_);
v___x_251_ = lean_nat_dec_le(v___x_249_, v___x_250_);
lean_dec(v___x_249_);
if (v___x_251_ == 0)
{
lean_object* v_val_252_; lean_object* v___x_254_; 
v_val_252_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_buckets_x27_245_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v_val_252_);
lean_ctor_set(v___x_240_, 0, v_size_x27_243_);
v___x_254_ = v___x_240_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_size_x27_243_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_val_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
else
{
lean_object* v___x_257_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v_buckets_x27_245_);
lean_ctor_set(v___x_240_, 0, v_size_x27_243_);
v___x_257_ = v___x_240_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_size_x27_243_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_buckets_x27_245_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_dec(v_b_220_);
lean_dec(v_a_219_);
return v_m_218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(lean_object* v_f_264_, lean_object* v_as_265_, size_t v_i_266_, size_t v_stop_267_, lean_object* v_b_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_eq(v_i_266_, v_stop_267_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_array_uget_borrowed(v_as_265_, v_i_266_);
lean_inc_ref(v_f_264_);
lean_inc_ref(v___y_269_);
lean_inc(v___x_272_);
v___x_273_ = lean_apply_3(v_f_264_, v___x_272_, v___y_269_, v___y_270_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_dec_ref(v_f_264_);
return v___x_273_;
}
else
{
lean_object* v_a_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; size_t v___x_277_; size_t v___x_278_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v_fst_275_ = lean_ctor_get(v_a_274_, 0);
lean_inc(v_fst_275_);
v_snd_276_ = lean_ctor_get(v_a_274_, 1);
lean_inc(v_snd_276_);
lean_dec(v_a_274_);
v___x_277_ = ((size_t)1ULL);
v___x_278_ = lean_usize_add(v_i_266_, v___x_277_);
v_i_266_ = v___x_278_;
v_b_268_ = v_fst_275_;
v___y_270_ = v_snd_276_;
goto _start;
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec_ref(v_f_264_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_b_268_);
lean_ctor_set(v___x_280_, 1, v___y_270_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed(lean_object* v_f_282_, lean_object* v_as_283_, lean_object* v_i_284_, lean_object* v_stop_285_, lean_object* v_b_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
size_t v_i_boxed_289_; size_t v_stop_boxed_290_; lean_object* v_res_291_; 
v_i_boxed_289_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_stop_boxed_290_ = lean_unbox_usize(v_stop_285_);
lean_dec(v_stop_285_);
v_res_291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_282_, v_as_283_, v_i_boxed_289_, v_stop_boxed_290_, v_b_286_, v___y_287_, v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec_ref(v_as_283_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(lean_object* v_f_292_, lean_object* v_as_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
if (lean_obj_tag(v_as_293_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec_ref(v_f_292_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___y_295_);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v_head_299_; lean_object* v_tail_300_; lean_object* v_ctor_301_; lean_object* v_rhs_302_; lean_object* v___x_303_; 
v_head_299_ = lean_ctor_get(v_as_293_, 0);
lean_inc(v_head_299_);
v_tail_300_ = lean_ctor_get(v_as_293_, 1);
lean_inc(v_tail_300_);
lean_dec_ref_known(v_as_293_, 2);
v_ctor_301_ = lean_ctor_get(v_head_299_, 0);
lean_inc(v_ctor_301_);
v_rhs_302_ = lean_ctor_get(v_head_299_, 2);
lean_inc_ref(v_rhs_302_);
lean_dec(v_head_299_);
lean_inc_ref(v_f_292_);
lean_inc_ref(v___y_294_);
v___x_303_ = lean_apply_3(v_f_292_, v_ctor_301_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_dec_ref(v_rhs_302_);
lean_dec(v_tail_300_);
lean_dec_ref(v_f_292_);
return v___x_303_;
}
else
{
lean_object* v_a_304_; lean_object* v_snd_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v_snd_305_ = lean_ctor_get(v_a_304_, 1);
lean_inc(v_snd_305_);
lean_dec(v_a_304_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = l_Lean_Expr_getUsedConstants(v_rhs_302_);
v___x_308_ = lean_array_get_size(v___x_307_);
v___x_309_ = lean_nat_dec_lt(v___x_306_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec_ref(v___x_307_);
v_as_293_ = v_tail_300_;
v___y_295_ = v_snd_305_;
goto _start;
}
else
{
lean_object* v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; 
v___x_311_ = lean_box(0);
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_308_);
lean_inc_ref(v_f_292_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_292_, v___x_307_, v___x_312_, v___x_313_, v___x_311_, v___y_294_, v_snd_305_);
lean_dec_ref(v___x_307_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_dec(v_tail_300_);
lean_dec_ref(v_f_292_);
return v___x_314_;
}
else
{
lean_object* v_a_315_; lean_object* v_snd_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v_snd_316_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_snd_316_);
lean_dec(v_a_315_);
v_as_293_ = v_tail_300_;
v___y_295_ = v_snd_316_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2___boxed(lean_object* v_f_318_, lean_object* v_as_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(v_f_318_, v_as_319_, v___y_320_, v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(lean_object* v_f_323_, lean_object* v_as_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
if (lean_obj_tag(v_as_324_) == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v_f_323_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___y_326_);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v_head_330_; lean_object* v_tail_331_; lean_object* v___x_332_; 
v_head_330_ = lean_ctor_get(v_as_324_, 0);
lean_inc(v_head_330_);
v_tail_331_ = lean_ctor_get(v_as_324_, 1);
lean_inc(v_tail_331_);
lean_dec_ref_known(v_as_324_, 2);
lean_inc_ref(v_f_323_);
lean_inc_ref(v___y_325_);
v___x_332_ = lean_apply_3(v_f_323_, v_head_330_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_dec(v_tail_331_);
lean_dec_ref(v_f_323_);
return v___x_332_;
}
else
{
lean_object* v_a_333_; lean_object* v_snd_334_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_332_, 1);
v_snd_334_ = lean_ctor_get(v_a_333_, 1);
lean_inc(v_snd_334_);
lean_dec(v_a_333_);
v_as_324_ = v_tail_331_;
v___y_326_ = v_snd_334_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1___boxed(lean_object* v_f_336_, lean_object* v_as_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_336_, v_as_337_, v___y_338_, v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(lean_object* v___x_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_341_);
lean_ctor_set(v___x_344_, 1, v___y_343_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0___boxed(lean_object* v___x_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(v___x_346_, v___y_347_, v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(lean_object* v_info_354_, lean_object* v_f_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___y_381_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_377_ = l_Lean_ConstantInfo_type(v_info_354_);
v___x_378_ = l_Lean_Expr_getUsedConstants(v___x_377_);
v___x_379_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_array_get_size(v___x_378_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_nat_dec_lt(v___x_379_, v___x_401_);
if (v___x_403_ == 0)
{
lean_object* v___f_404_; 
lean_dec_ref(v___x_378_);
v___f_404_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___closed__0));
v___y_381_ = v___f_404_;
goto v___jp_380_;
}
else
{
size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_405_ = lean_usize_of_nat(v___x_401_);
v___x_406_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1));
v___x_407_ = lean_box_usize(v___x_405_);
lean_inc_ref(v_f_355_);
v___x_408_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed), 7, 5);
lean_closure_set(v___x_408_, 0, v_f_355_);
lean_closure_set(v___x_408_, 1, v___x_378_);
lean_closure_set(v___x_408_, 2, v___x_406_);
lean_closure_set(v___x_408_, 3, v___x_407_);
lean_closure_set(v___x_408_, 4, v___x_402_);
v___y_381_ = v___x_408_;
goto v___jp_380_;
}
v___jp_358_:
{
switch(lean_obj_tag(v_info_354_))
{
case 5:
{
lean_object* v_val_361_; lean_object* v_all_362_; lean_object* v_ctors_363_; lean_object* v___x_364_; 
v_val_361_ = lean_ctor_get(v_info_354_, 0);
lean_inc_ref(v_val_361_);
lean_dec_ref_known(v_info_354_, 1);
v_all_362_ = lean_ctor_get(v_val_361_, 3);
lean_inc(v_all_362_);
v_ctors_363_ = lean_ctor_get(v_val_361_, 4);
lean_inc(v_ctors_363_);
lean_dec_ref(v_val_361_);
lean_inc_ref(v_f_355_);
v___x_364_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_355_, v_ctors_363_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_dec(v_all_362_);
lean_dec_ref(v_f_355_);
return v___x_364_;
}
else
{
lean_object* v_a_365_; lean_object* v_snd_366_; lean_object* v___x_367_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
lean_dec_ref_known(v___x_364_, 1);
v_snd_366_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_snd_366_);
lean_dec(v_a_365_);
v___x_367_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_355_, v_all_362_, v___y_359_, v_snd_366_);
return v___x_367_;
}
}
case 6:
{
lean_object* v_val_368_; lean_object* v_induct_369_; lean_object* v___x_370_; 
v_val_368_ = lean_ctor_get(v_info_354_, 0);
lean_inc_ref(v_val_368_);
lean_dec_ref_known(v_info_354_, 1);
v_induct_369_ = lean_ctor_get(v_val_368_, 1);
lean_inc(v_induct_369_);
lean_dec_ref(v_val_368_);
lean_inc_ref(v___y_359_);
v___x_370_ = lean_apply_3(v_f_355_, v_induct_369_, v___y_359_, v___y_360_);
return v___x_370_;
}
case 7:
{
lean_object* v_val_371_; lean_object* v_rules_372_; lean_object* v___x_373_; 
v_val_371_ = lean_ctor_get(v_info_354_, 0);
lean_inc_ref(v_val_371_);
lean_dec_ref_known(v_info_354_, 1);
v_rules_372_ = lean_ctor_get(v_val_371_, 6);
lean_inc(v_rules_372_);
lean_dec_ref(v_val_371_);
v___x_373_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(v_f_355_, v_rules_372_, v___y_359_, v___y_360_);
return v___x_373_;
}
default: 
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v_f_355_);
lean_dec_ref(v_info_354_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___y_360_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
}
v___jp_380_:
{
lean_object* v___x_382_; 
lean_inc_ref(v___y_356_);
v___x_382_ = lean_apply_2(v___y_381_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_dec_ref(v_f_355_);
lean_dec_ref(v_info_354_);
return v___x_382_;
}
else
{
lean_object* v_a_383_; lean_object* v_snd_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v_snd_384_ = lean_ctor_get(v_a_383_, 1);
lean_inc(v_snd_384_);
lean_dec(v_a_383_);
v___x_385_ = l_Lean_ConstantInfo_name(v_info_354_);
lean_inc_ref(v_f_355_);
lean_inc_ref(v___y_356_);
v___x_386_ = lean_apply_3(v_f_355_, v___x_385_, v___y_356_, v_snd_384_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_dec_ref(v_f_355_);
lean_dec_ref(v_info_354_);
return v___x_386_;
}
else
{
lean_object* v_a_387_; lean_object* v_snd_388_; uint8_t v___x_389_; lean_object* v___x_390_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v_snd_388_ = lean_ctor_get(v_a_387_, 1);
lean_inc(v_snd_388_);
lean_dec(v_a_387_);
v___x_389_ = 1;
lean_inc_ref(v_info_354_);
v___x_390_ = l_Lean_ConstantInfo_value_x3f(v_info_354_, v___x_389_);
if (lean_obj_tag(v___x_390_) == 1)
{
lean_object* v_val_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_val_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_val_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = l_Lean_Expr_getUsedConstants(v_val_391_);
v___x_393_ = lean_array_get_size(v___x_392_);
v___x_394_ = lean_nat_dec_lt(v___x_379_, v___x_393_);
if (v___x_394_ == 0)
{
lean_dec_ref(v___x_392_);
v___y_359_ = v___y_356_;
v___y_360_ = v_snd_388_;
goto v___jp_358_;
}
else
{
lean_object* v___x_395_; size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_box(0);
v___x_396_ = ((size_t)0ULL);
v___x_397_ = lean_usize_of_nat(v___x_393_);
lean_inc_ref(v_f_355_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_355_, v___x_392_, v___x_396_, v___x_397_, v___x_395_, v___y_356_, v_snd_388_);
lean_dec_ref(v___x_392_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_dec_ref(v_f_355_);
lean_dec_ref(v_info_354_);
return v___x_398_;
}
else
{
lean_object* v_a_399_; lean_object* v_snd_400_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v_snd_400_ = lean_ctor_get(v_a_399_, 1);
lean_inc(v_snd_400_);
lean_dec(v_a_399_);
v___y_359_ = v___y_356_;
v___y_360_ = v_snd_400_;
goto v___jp_358_;
}
}
}
else
{
lean_dec(v___x_390_);
v___y_359_ = v___y_356_;
v___y_360_ = v_snd_388_;
goto v___jp_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed(lean_object* v_info_409_, lean_object* v_f_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(v_info_409_, v_f_410_, v___y_411_, v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_worklist_417_; lean_object* v_checked_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint8_t v___x_421_; 
v_worklist_417_ = lean_ctor_get(v_a_416_, 0);
v_checked_418_ = lean_ctor_get(v_a_416_, 1);
v___x_419_ = lean_array_get_size(v_worklist_417_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_nat_dec_eq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_462_; 
lean_inc_ref(v_checked_418_);
lean_inc_ref(v_worklist_417_);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; lean_object* v_unused_464_; 
v_unused_463_ = lean_ctor_get(v_a_416_, 1);
lean_dec(v_unused_463_);
v_unused_464_ = lean_ctor_get(v_a_416_, 0);
lean_dec(v_unused_464_);
v___x_423_ = v_a_416_;
v_isShared_424_ = v_isSharedCheck_462_;
goto v_resetjp_422_;
}
else
{
lean_dec(v_a_416_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_462_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_425_ = lean_box(0);
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_sub(v___x_419_, v___x_426_);
v___x_428_ = lean_array_get(v___x_425_, v_worklist_417_, v___x_427_);
lean_dec(v___x_427_);
v___x_429_ = lean_array_pop(v_worklist_417_);
lean_inc_ref(v_checked_418_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_431_ = v___x_423_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_checked_418_);
v___x_431_ = v_reuseFailAlloc_461_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
uint8_t v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_checked_418_, v___x_428_);
lean_dec_ref(v_checked_418_);
if (v___x_432_ == 0)
{
lean_object* v_solution_433_; lean_object* v_constMap_434_; lean_object* v___x_435_; 
v_solution_433_ = lean_ctor_get(v_a_415_, 0);
v_constMap_434_ = lean_ctor_get(v_solution_433_, 0);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_434_, v___x_428_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___closed__0));
v___x_438_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(v_val_436_, v___x_437_, v_a_415_, v___x_431_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_dec(v___x_428_);
return v___x_438_;
}
else
{
lean_object* v_a_439_; lean_object* v_snd_440_; lean_object* v_worklist_441_; lean_object* v_checked_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_452_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v_snd_440_ = lean_ctor_get(v_a_439_, 1);
lean_inc(v_snd_440_);
lean_dec(v_a_439_);
v_worklist_441_ = lean_ctor_get(v_snd_440_, 0);
v_checked_442_ = lean_ctor_get(v_snd_440_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_snd_440_);
if (v_isSharedCheck_452_ == 0)
{
v___x_444_ = v_snd_440_;
v_isShared_445_ = v_isSharedCheck_452_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_checked_442_);
lean_inc(v_worklist_441_);
lean_dec(v_snd_440_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_452_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_446_ = lean_box(0);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_checked_442_, v___x_428_, v___x_446_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_447_);
v___x_449_ = v___x_444_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_worklist_441_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_451_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
v_a_416_ = v___x_449_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_435_);
lean_dec_ref(v___x_431_);
v___x_453_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2));
v___x_454_ = 1;
v___x_455_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_428_, v___x_454_);
v___x_456_ = lean_string_append(v___x_453_, v___x_455_);
lean_dec_ref(v___x_455_);
v___x_457_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_458_ = lean_string_append(v___x_456_, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
else
{
lean_dec(v___x_428_);
v_a_416_ = v___x_431_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_a_416_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___boxed(lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v_a_468_, v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1(lean_object* v_00_u03b2_471_, lean_object* v_m_472_, lean_object* v_a_473_, lean_object* v_b_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_m_472_, v_a_473_, v_b_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4(lean_object* v_00_u03b2_476_, lean_object* v_data_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_data_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_479_, lean_object* v_i_480_, lean_object* v_source_481_, lean_object* v_target_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(v_i_480_, v_source_481_, v_target_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(v_x_485_, v_x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(lean_object* v_f_488_, lean_object* v_as_489_, size_t v_i_490_, size_t v_stop_491_, lean_object* v_b_492_, lean_object* v___y_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_eq(v_i_490_, v_stop_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_fst_497_; lean_object* v_snd_498_; size_t v___x_499_; size_t v___x_500_; 
v___x_495_ = lean_array_uget_borrowed(v_as_489_, v_i_490_);
lean_inc_ref(v_f_488_);
lean_inc(v___x_495_);
v___x_496_ = lean_apply_2(v_f_488_, v___x_495_, v___y_493_);
v_fst_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_fst_497_);
v_snd_498_ = lean_ctor_get(v___x_496_, 1);
lean_inc(v_snd_498_);
lean_dec_ref(v___x_496_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_490_, v___x_499_);
v_i_490_ = v___x_500_;
v_b_492_ = v_fst_497_;
v___y_493_ = v_snd_498_;
goto _start;
}
else
{
lean_object* v___x_502_; 
lean_dec_ref(v_f_488_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_b_492_);
lean_ctor_set(v___x_502_, 1, v___y_493_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed(lean_object* v_f_503_, lean_object* v_as_504_, lean_object* v_i_505_, lean_object* v_stop_506_, lean_object* v_b_507_, lean_object* v___y_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; lean_object* v_res_511_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_505_);
lean_dec(v_i_505_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_506_);
lean_dec(v_stop_506_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_503_, v_as_504_, v_i_boxed_509_, v_stop_boxed_510_, v_b_507_, v___y_508_);
lean_dec_ref(v_as_504_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(lean_object* v_f_512_, lean_object* v_as_513_, lean_object* v___y_514_){
_start:
{
if (lean_obj_tag(v_as_513_) == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref(v_f_512_);
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___y_514_);
return v___x_516_;
}
else
{
lean_object* v_head_517_; lean_object* v_tail_518_; lean_object* v_ctor_519_; lean_object* v_rhs_520_; lean_object* v___x_521_; lean_object* v_snd_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_head_517_ = lean_ctor_get(v_as_513_, 0);
lean_inc(v_head_517_);
v_tail_518_ = lean_ctor_get(v_as_513_, 1);
lean_inc(v_tail_518_);
lean_dec_ref_known(v_as_513_, 2);
v_ctor_519_ = lean_ctor_get(v_head_517_, 0);
lean_inc(v_ctor_519_);
v_rhs_520_ = lean_ctor_get(v_head_517_, 2);
lean_inc_ref(v_rhs_520_);
lean_dec(v_head_517_);
lean_inc_ref(v_f_512_);
v___x_521_ = lean_apply_2(v_f_512_, v_ctor_519_, v___y_514_);
v_snd_522_ = lean_ctor_get(v___x_521_, 1);
lean_inc(v_snd_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = l_Lean_Expr_getUsedConstants(v_rhs_520_);
v___x_525_ = lean_array_get_size(v___x_524_);
v___x_526_ = lean_nat_dec_lt(v___x_523_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v___x_524_);
v_as_513_ = v_tail_518_;
v___y_514_ = v_snd_522_;
goto _start;
}
else
{
lean_object* v___x_528_; size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v_snd_532_; 
v___x_528_ = lean_box(0);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_525_);
lean_inc_ref(v_f_512_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_512_, v___x_524_, v___x_529_, v___x_530_, v___x_528_, v_snd_522_);
lean_dec_ref(v___x_524_);
v_snd_532_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_532_);
lean_dec_ref(v___x_531_);
v_as_513_ = v_tail_518_;
v___y_514_ = v_snd_532_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(lean_object* v_f_534_, lean_object* v_as_535_, lean_object* v___y_536_){
_start:
{
if (lean_obj_tag(v_as_535_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref(v_f_534_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___y_536_);
return v___x_538_;
}
else
{
lean_object* v_head_539_; lean_object* v_tail_540_; lean_object* v___x_541_; lean_object* v_snd_542_; 
v_head_539_ = lean_ctor_get(v_as_535_, 0);
lean_inc(v_head_539_);
v_tail_540_ = lean_ctor_get(v_as_535_, 1);
lean_inc(v_tail_540_);
lean_dec_ref_known(v_as_535_, 2);
lean_inc_ref(v_f_534_);
v___x_541_ = lean_apply_2(v_f_534_, v_head_539_, v___y_536_);
v_snd_542_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_snd_542_);
lean_dec_ref(v___x_541_);
v_as_535_ = v_tail_540_;
v___y_536_ = v_snd_542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___lam__0(lean_object* v___x_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___y_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(lean_object* v_info_549_, lean_object* v_f_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___y_553_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___y_572_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_568_ = l_Lean_ConstantInfo_type(v_info_549_);
v___x_569_ = l_Lean_Expr_getUsedConstants(v___x_568_);
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_array_get_size(v___x_569_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_nat_dec_lt(v___x_570_, v___x_589_);
if (v___x_591_ == 0)
{
lean_object* v___f_592_; 
lean_dec_ref(v___x_569_);
v___f_592_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___closed__0));
v___y_572_ = v___f_592_;
goto v___jp_571_;
}
else
{
size_t v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_usize_of_nat(v___x_589_);
v___x_594_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1));
v___x_595_ = lean_box_usize(v___x_593_);
lean_inc_ref(v_f_550_);
v___x_596_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed), 6, 5);
lean_closure_set(v___x_596_, 0, v_f_550_);
lean_closure_set(v___x_596_, 1, v___x_569_);
lean_closure_set(v___x_596_, 2, v___x_594_);
lean_closure_set(v___x_596_, 3, v___x_595_);
lean_closure_set(v___x_596_, 4, v___x_590_);
v___y_572_ = v___x_596_;
goto v___jp_571_;
}
v___jp_552_:
{
switch(lean_obj_tag(v_info_549_))
{
case 5:
{
lean_object* v_val_554_; lean_object* v_all_555_; lean_object* v_ctors_556_; lean_object* v___x_557_; lean_object* v_snd_558_; lean_object* v___x_559_; 
v_val_554_ = lean_ctor_get(v_info_549_, 0);
lean_inc_ref(v_val_554_);
lean_dec_ref_known(v_info_549_, 1);
v_all_555_ = lean_ctor_get(v_val_554_, 3);
lean_inc(v_all_555_);
v_ctors_556_ = lean_ctor_get(v_val_554_, 4);
lean_inc(v_ctors_556_);
lean_dec_ref(v_val_554_);
lean_inc_ref(v_f_550_);
v___x_557_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(v_f_550_, v_ctors_556_, v___y_553_);
v_snd_558_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_snd_558_);
lean_dec_ref(v___x_557_);
v___x_559_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(v_f_550_, v_all_555_, v_snd_558_);
return v___x_559_;
}
case 6:
{
lean_object* v_val_560_; lean_object* v_induct_561_; lean_object* v___x_562_; 
v_val_560_ = lean_ctor_get(v_info_549_, 0);
lean_inc_ref(v_val_560_);
lean_dec_ref_known(v_info_549_, 1);
v_induct_561_ = lean_ctor_get(v_val_560_, 1);
lean_inc(v_induct_561_);
lean_dec_ref(v_val_560_);
v___x_562_ = lean_apply_2(v_f_550_, v_induct_561_, v___y_553_);
return v___x_562_;
}
case 7:
{
lean_object* v_val_563_; lean_object* v_rules_564_; lean_object* v___x_565_; 
v_val_563_ = lean_ctor_get(v_info_549_, 0);
lean_inc_ref(v_val_563_);
lean_dec_ref_known(v_info_549_, 1);
v_rules_564_ = lean_ctor_get(v_val_563_, 6);
lean_inc(v_rules_564_);
lean_dec_ref(v_val_563_);
v___x_565_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(v_f_550_, v_rules_564_, v___y_553_);
return v___x_565_;
}
default: 
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v_f_550_);
lean_dec_ref(v_info_549_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___y_553_);
return v___x_567_;
}
}
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v_snd_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_snd_577_; uint8_t v___x_578_; lean_object* v___x_579_; 
v___x_573_ = lean_apply_1(v___y_572_, v___y_551_);
v_snd_574_ = lean_ctor_get(v___x_573_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v___x_573_);
v___x_575_ = l_Lean_ConstantInfo_name(v_info_549_);
lean_inc_ref(v_f_550_);
v___x_576_ = lean_apply_2(v_f_550_, v___x_575_, v_snd_574_);
v_snd_577_ = lean_ctor_get(v___x_576_, 1);
lean_inc(v_snd_577_);
lean_dec_ref(v___x_576_);
v___x_578_ = 1;
lean_inc_ref(v_info_549_);
v___x_579_ = l_Lean_ConstantInfo_value_x3f(v_info_549_, v___x_578_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_val_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = l_Lean_Expr_getUsedConstants(v_val_580_);
v___x_582_ = lean_array_get_size(v___x_581_);
v___x_583_ = lean_nat_dec_lt(v___x_570_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec_ref(v___x_581_);
v___y_553_ = v_snd_577_;
goto v___jp_552_;
}
else
{
lean_object* v___x_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; lean_object* v_snd_588_; 
v___x_584_ = lean_box(0);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_582_);
lean_inc_ref(v_f_550_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_550_, v___x_581_, v___x_585_, v___x_586_, v___x_584_, v_snd_577_);
lean_dec_ref(v___x_581_);
v_snd_588_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v___x_587_);
v___y_553_ = v_snd_588_;
goto v___jp_552_;
}
}
else
{
lean_dec(v___x_579_);
v___y_553_ = v_snd_577_;
goto v___jp_552_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(lean_object* v_a_597_, lean_object* v_constMap_598_, lean_object* v___x_599_, lean_object* v_ref_600_, lean_object* v___y_601_){
_start:
{
uint8_t v___x_602_; 
v___x_602_ = lean_name_eq(v_ref_600_, v_a_597_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_598_, v_ref_600_);
if (lean_obj_tag(v___x_603_) == 1)
{
lean_object* v_val_604_; 
v_val_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v___x_603_, 1);
if (lean_obj_tag(v_val_604_) == 0)
{
lean_object* v_fst_605_; lean_object* v_snd_606_; uint8_t v___x_607_; 
lean_dec_ref_known(v_val_604_, 1);
v_fst_605_ = lean_ctor_get(v___y_601_, 0);
v_snd_606_ = lean_ctor_get(v___y_601_, 1);
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_fst_605_, v_ref_600_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_618_; 
lean_inc(v_snd_606_);
lean_inc(v_fst_605_);
v_isSharedCheck_618_ = !lean_is_exclusive(v___y_601_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_619_ = lean_ctor_get(v___y_601_, 1);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v___y_601_, 0);
lean_dec(v_unused_620_);
v___x_609_ = v___y_601_;
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___y_601_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_618_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
lean_inc(v_ref_600_);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_fst_605_, v_ref_600_, v___x_599_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_a_597_);
lean_ctor_set(v___x_609_, 0, v_ref_600_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_ref_600_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_a_597_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_array_push(v_snd_606_, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_611_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_599_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
return v___x_616_;
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec(v_ref_600_);
lean_dec(v_a_597_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_599_);
lean_ctor_set(v___x_621_, 1, v___y_601_);
return v___x_621_;
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_val_604_);
lean_dec(v_ref_600_);
lean_dec(v_a_597_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_599_);
lean_ctor_set(v___x_622_, 1, v___y_601_);
return v___x_622_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v___x_603_);
lean_dec(v_ref_600_);
lean_dec(v_a_597_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_599_);
lean_ctor_set(v___x_623_, 1, v___y_601_);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v_ref_600_);
lean_dec(v_a_597_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_599_);
lean_ctor_set(v___x_624_, 1, v___y_601_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed(lean_object* v_a_625_, lean_object* v_constMap_626_, lean_object* v___x_627_, lean_object* v_ref_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(v_a_625_, v_constMap_626_, v___x_627_, v_ref_628_, v___y_629_);
lean_dec_ref(v_constMap_626_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(lean_object* v_env_631_, lean_object* v_as_632_, size_t v_sz_633_, size_t v_i_634_, lean_object* v_b_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_a_638_; lean_object* v_snd_639_; uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_lt(v_i_634_, v_sz_633_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v_env_631_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_b_635_);
lean_ctor_set(v___x_644_, 1, v___y_636_);
return v___x_644_;
}
else
{
lean_object* v_constMap_645_; lean_object* v___x_646_; lean_object* v_a_647_; lean_object* v___x_648_; 
v_constMap_645_ = lean_ctor_get(v_env_631_, 0);
v___x_646_ = lean_box(0);
v_a_647_ = lean_array_uget_borrowed(v_as_632_, v_i_634_);
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_645_, v_a_647_);
if (lean_obj_tag(v___x_648_) == 1)
{
lean_object* v_val_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v_snd_652_; 
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v___x_648_, 1);
lean_inc_ref(v_constMap_645_);
lean_inc(v_a_647_);
v___f_650_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_650_, 0, v_a_647_);
lean_closure_set(v___f_650_, 1, v_constMap_645_);
lean_closure_set(v___f_650_, 2, v___x_646_);
v___x_651_ = l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(v_val_649_, v___f_650_, v___y_636_);
v_snd_652_ = lean_ctor_get(v___x_651_, 1);
lean_inc(v_snd_652_);
lean_dec_ref(v___x_651_);
v_a_638_ = v___x_646_;
v_snd_639_ = v_snd_652_;
goto v___jp_637_;
}
else
{
lean_dec(v___x_648_);
v_a_638_ = v___x_646_;
v_snd_639_ = v___y_636_;
goto v___jp_637_;
}
}
v___jp_637_:
{
size_t v___x_640_; size_t v___x_641_; 
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_add(v_i_634_, v___x_640_);
v_i_634_ = v___x_641_;
v_b_635_ = v_a_638_;
v___y_636_ = v_snd_639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___boxed(lean_object* v_env_653_, lean_object* v_as_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_b_657_, lean_object* v___y_658_){
_start:
{
size_t v_sz_boxed_659_; size_t v_i_boxed_660_; lean_object* v_res_661_; 
v_sz_boxed_659_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_660_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_653_, v_as_654_, v_sz_boxed_659_, v_i_boxed_660_, v_b_657_, v___y_658_);
lean_dec_ref(v_as_654_);
return v_res_661_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__0(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_box(0);
v___x_663_ = lean_unsigned_to_nat(16u);
v___x_664_ = lean_mk_array(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__0, &l_Lake_Check_usedAxioms___closed__0_once, _init_l_Lake_Check_usedAxioms___closed__0);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__3(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((lean_object*)(l_Lake_Check_usedAxioms___closed__2));
v___x_671_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_usedAxioms(lean_object* v_env_673_){
_start:
{
lean_object* v_constOrder_674_; lean_object* v___x_675_; size_t v_sz_676_; size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_snd_680_; lean_object* v_snd_681_; 
v_constOrder_674_ = lean_ctor_get(v_env_673_, 1);
lean_inc_ref(v_constOrder_674_);
v___x_675_ = lean_box(0);
v_sz_676_ = lean_array_size(v_constOrder_674_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__3, &l_Lake_Check_usedAxioms___closed__3_once, _init_l_Lake_Check_usedAxioms___closed__3);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_673_, v_constOrder_674_, v_sz_676_, v___x_677_, v___x_675_, v___x_678_);
lean_dec_ref(v_constOrder_674_);
v_snd_680_ = lean_ctor_get(v___x_679_, 1);
lean_inc(v_snd_680_);
lean_dec_ref(v___x_679_);
v_snd_681_ = lean_ctor_get(v_snd_680_, 1);
lean_inc(v_snd_681_);
lean_dec(v_snd_680_);
return v_snd_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(lean_object* v_as_682_, size_t v_sz_683_, size_t v_i_684_, lean_object* v_b_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_686_ == 0)
{
return v_b_685_;
}
else
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v_r_689_; size_t v___x_690_; size_t v___x_691_; 
v_a_687_ = lean_array_uget_borrowed(v_as_682_, v_i_684_);
v___x_688_ = lean_box(0);
lean_inc(v_a_687_);
v_r_689_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_b_685_, v_a_687_, v___x_688_);
v___x_690_ = ((size_t)1ULL);
v___x_691_ = lean_usize_add(v_i_684_, v___x_690_);
v_i_684_ = v___x_691_;
v_b_685_ = v_r_689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2___boxed(lean_object* v_as_693_, lean_object* v_sz_694_, lean_object* v_i_695_, lean_object* v_b_696_){
_start:
{
size_t v_sz_boxed_697_; size_t v_i_boxed_698_; lean_object* v_res_699_; 
v_sz_boxed_697_ = lean_unbox_usize(v_sz_694_);
lean_dec(v_sz_694_);
v_i_boxed_698_ = lean_unbox_usize(v_i_695_);
lean_dec(v_i_695_);
v_res_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_as_693_, v_sz_boxed_697_, v_i_boxed_698_, v_b_696_);
lean_dec_ref(v_as_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(lean_object* v_m_700_, lean_object* v_l_701_){
_start:
{
size_t v_sz_702_; size_t v___x_703_; lean_object* v___x_704_; 
v_sz_702_ = lean_array_size(v_l_701_);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_l_701_, v_sz_702_, v___x_703_, v_m_700_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2___boxed(lean_object* v_m_705_, lean_object* v_l_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v_m_705_, v_l_706_);
lean_dec_ref(v_l_706_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(lean_object* v_solution_710_, lean_object* v_as_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_b_714_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v_b_714_);
return v___x_716_;
}
else
{
lean_object* v_constMap_717_; lean_object* v_a_718_; lean_object* v___x_719_; 
v_constMap_717_ = lean_ctor_get(v_solution_710_, 0);
v_a_718_ = lean_array_uget_borrowed(v_as_711_, v_i_713_);
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_717_, v_a_718_);
if (lean_obj_tag(v___x_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_739_; 
v_val_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_739_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_739_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_val_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_739_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
if (lean_obj_tag(v_val_720_) == 2)
{
lean_object* v_val_724_; lean_object* v_toConstantVal_725_; lean_object* v_name_726_; lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; 
lean_del_object(v___x_722_);
v_val_724_ = lean_ctor_get(v_val_720_, 0);
lean_inc_ref(v_val_724_);
lean_dec_ref_known(v_val_720_, 1);
v_toConstantVal_725_ = lean_ctor_get(v_val_724_, 0);
lean_inc_ref(v_toConstantVal_725_);
lean_dec_ref(v_val_724_);
v_name_726_ = lean_ctor_get(v_toConstantVal_725_, 0);
lean_inc(v_name_726_);
lean_dec_ref(v_toConstantVal_725_);
v___x_727_ = lean_array_push(v_b_714_, v_name_726_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_713_, v___x_728_);
v_i_713_ = v___x_729_;
v_b_714_ = v___x_727_;
goto _start;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_dec(v_val_720_);
lean_dec_ref(v_b_714_);
v___x_731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0));
lean_inc(v_a_718_);
v___x_732_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_718_, v___x_715_);
v___x_733_ = lean_string_append(v___x_731_, v___x_732_);
lean_dec_ref(v___x_732_);
v___x_734_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_735_ = lean_string_append(v___x_733_, v___x_734_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
lean_ctor_set(v___x_722_, 0, v___x_735_);
v___x_737_ = v___x_722_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
lean_dec(v___x_719_);
lean_dec_ref(v_b_714_);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_718_);
v___x_741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_718_, v___x_715_);
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_744_ = lean_string_append(v___x_742_, v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___boxed(lean_object* v_solution_746_, lean_object* v_as_747_, lean_object* v_sz_748_, lean_object* v_i_749_, lean_object* v_b_750_){
_start:
{
size_t v_sz_boxed_751_; size_t v_i_boxed_752_; lean_object* v_res_753_; 
v_sz_boxed_751_ = lean_unbox_usize(v_sz_748_);
lean_dec(v_sz_748_);
v_i_boxed_752_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_746_, v_as_747_, v_sz_boxed_751_, v_i_boxed_752_, v_b_750_);
lean_dec_ref(v_as_747_);
lean_dec_ref(v_solution_746_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(lean_object* v_solution_755_, lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_b_759_);
return v___x_761_;
}
else
{
lean_object* v_constMap_762_; lean_object* v_a_763_; lean_object* v___x_764_; 
v_constMap_762_ = lean_ctor_get(v_solution_755_, 0);
v_a_763_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_762_, v_a_763_);
if (lean_obj_tag(v___x_764_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_784_; 
v_val_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_784_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_784_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_val_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_784_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
if (lean_obj_tag(v_val_765_) == 1)
{
lean_object* v_val_769_; lean_object* v_toConstantVal_770_; lean_object* v_name_771_; lean_object* v___x_772_; size_t v___x_773_; size_t v___x_774_; 
lean_del_object(v___x_767_);
v_val_769_ = lean_ctor_get(v_val_765_, 0);
lean_inc_ref(v_val_769_);
lean_dec_ref_known(v_val_765_, 1);
v_toConstantVal_770_ = lean_ctor_get(v_val_769_, 0);
lean_inc_ref(v_toConstantVal_770_);
lean_dec_ref(v_val_769_);
v_name_771_ = lean_ctor_get(v_toConstantVal_770_, 0);
lean_inc(v_name_771_);
lean_dec_ref(v_toConstantVal_770_);
v___x_772_ = lean_array_push(v_b_759_, v_name_771_);
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_758_, v___x_773_);
v_i_758_ = v___x_774_;
v_b_759_ = v___x_772_;
goto _start;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v_val_765_);
lean_dec_ref(v_b_759_);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0));
lean_inc(v_a_763_);
v___x_777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_763_, v___x_760_);
v___x_778_ = lean_string_append(v___x_776_, v___x_777_);
lean_dec_ref(v___x_777_);
v___x_779_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_780_ = lean_string_append(v___x_778_, v___x_779_);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 0);
lean_ctor_set(v___x_767_, 0, v___x_780_);
v___x_782_ = v___x_767_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v___x_764_);
lean_dec_ref(v_b_759_);
v___x_785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_763_);
v___x_786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_763_, v___x_760_);
v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
lean_dec_ref(v___x_786_);
v___x_788_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___boxed(lean_object* v_solution_791_, lean_object* v_as_792_, lean_object* v_sz_793_, lean_object* v_i_794_, lean_object* v_b_795_){
_start:
{
size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v_sz_boxed_796_ = lean_unbox_usize(v_sz_793_);
lean_dec(v_sz_793_);
v_i_boxed_797_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_791_, v_as_792_, v_sz_boxed_796_, v_i_boxed_797_, v_b_795_);
lean_dec_ref(v_as_792_);
lean_dec_ref(v_solution_791_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms(lean_object* v_solution_801_, lean_object* v_theoremTargets_802_, lean_object* v_definitionTargets_803_, lean_object* v_legalAxioms_804_){
_start:
{
lean_object* v_worklist_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_worklist_805_ = ((lean_object*)(l_Lake_Check_checkAxioms___closed__0));
v_sz_806_ = lean_array_size(v_theoremTargets_802_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_801_, v_theoremTargets_802_, v_sz_806_, v___x_807_, v_worklist_805_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_solution_801_);
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; size_t v_sz_818_; lean_object* v___x_819_; 
v_a_817_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_808_, 1);
v_sz_818_ = lean_array_size(v_definitionTargets_803_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_801_, v_definitionTargets_803_, v_sz_818_, v___x_807_, v_a_817_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_solution_801_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_a_828_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_819_, 1);
v___x_829_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v___x_829_, v_legalAxioms_804_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_solution_801_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_a_828_);
lean_ctor_set(v___x_832_, 1, v___x_829_);
v___x_833_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v___x_831_, v___x_832_);
lean_dec_ref_known(v___x_831_, 2);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_a_842_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_850_ == 0)
{
v___x_844_ = v___x_833_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_833_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v___x_848_; 
v_fst_846_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_fst_846_);
lean_dec(v_a_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_fst_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms___boxed(lean_object* v_solution_851_, lean_object* v_theoremTargets_852_, lean_object* v_definitionTargets_853_, lean_object* v_legalAxioms_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lake_Check_checkAxioms(v_solution_851_, v_theoremTargets_852_, v_definitionTargets_853_, v_legalAxioms_854_);
lean_dec_ref(v_legalAxioms_854_);
lean_dec_ref(v_definitionTargets_853_);
lean_dec_ref(v_theoremTargets_852_);
return v_res_855_;
}
}
lean_object* runtime_initialize_LeanExport_Parse(uint8_t builtin);
lean_object* runtime_initialize_Lake_Check_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Check_Axioms(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Lake_Check_Axioms(uint8_t builtin) {
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
LEAN_EXPORT lean_object* initialize_Lake_Check_Axioms(uint8_t builtin) {
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
res = runtime_initialize_Lake_Check_Axioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Check_Axioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Check_Axioms(builtin);
}
#ifdef __cplusplus
}
#endif
