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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_nbuckets_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_211_ = lean_array_get_size(v_data_210_);
v___x_212_ = lean_unsigned_to_nat(2u);
v_nbuckets_213_ = lean_nat_mul(v___x_211_, v___x_212_);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_box(0);
v___x_216_ = lean_mk_array(v_nbuckets_213_, v___x_215_);
v___x_217_ = lean_array_propagate_mark(v_data_210_, v___x_216_);
v___x_218_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(v___x_214_, v_data_210_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(lean_object* v_m_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v_size_222_; lean_object* v_buckets_223_; lean_object* v___x_224_; uint64_t v___y_226_; 
v_size_222_ = lean_ctor_get(v_m_219_, 0);
v_buckets_223_ = lean_ctor_get(v_m_219_, 1);
v___x_224_ = lean_array_get_size(v_buckets_223_);
if (lean_obj_tag(v_a_220_) == 0)
{
uint64_t v___x_263_; 
v___x_263_ = 1723ULL;
v___y_226_ = v___x_263_;
goto v___jp_225_;
}
else
{
uint64_t v_hash_264_; 
v_hash_264_ = lean_ctor_get_uint64(v_a_220_, sizeof(void*)*2);
v___y_226_ = v_hash_264_;
goto v___jp_225_;
}
v___jp_225_:
{
uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v_fold_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; size_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; lean_object* v_bkt_238_; uint8_t v___x_239_; 
v___x_227_ = 32ULL;
v___x_228_ = lean_uint64_shift_right(v___y_226_, v___x_227_);
v_fold_229_ = lean_uint64_xor(v___y_226_, v___x_228_);
v___x_230_ = 16ULL;
v___x_231_ = lean_uint64_shift_right(v_fold_229_, v___x_230_);
v___x_232_ = lean_uint64_xor(v_fold_229_, v___x_231_);
v___x_233_ = lean_uint64_to_usize(v___x_232_);
v___x_234_ = lean_usize_of_nat(v___x_224_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_sub(v___x_234_, v___x_235_);
v___x_237_ = lean_usize_land(v___x_233_, v___x_236_);
v_bkt_238_ = lean_array_uget_borrowed(v_buckets_223_, v___x_237_);
v___x_239_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_220_, v_bkt_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_260_; 
lean_inc_ref(v_buckets_223_);
lean_inc(v_size_222_);
v_isSharedCheck_260_ = !lean_is_exclusive(v_m_219_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; 
v_unused_261_ = lean_ctor_get(v_m_219_, 1);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_m_219_, 0);
lean_dec(v_unused_262_);
v___x_241_ = v_m_219_;
v_isShared_242_ = v_isSharedCheck_260_;
goto v_resetjp_240_;
}
else
{
lean_dec(v_m_219_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_260_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v_size_x27_244_; lean_object* v___x_245_; lean_object* v_buckets_x27_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v_size_x27_244_ = lean_nat_add(v_size_222_, v___x_243_);
lean_dec(v_size_222_);
lean_inc(v_bkt_238_);
v___x_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_245_, 0, v_a_220_);
lean_ctor_set(v___x_245_, 1, v_b_221_);
lean_ctor_set(v___x_245_, 2, v_bkt_238_);
v_buckets_x27_246_ = lean_array_uset(v_buckets_223_, v___x_237_, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(4u);
v___x_248_ = lean_nat_mul(v_size_x27_244_, v___x_247_);
v___x_249_ = lean_unsigned_to_nat(3u);
v___x_250_ = lean_nat_div(v___x_248_, v___x_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_array_get_size(v_buckets_x27_246_);
v___x_252_ = lean_nat_dec_le(v___x_250_, v___x_251_);
lean_dec(v___x_250_);
if (v___x_252_ == 0)
{
lean_object* v_val_253_; lean_object* v___x_255_; 
v_val_253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_buckets_x27_246_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_val_253_);
lean_ctor_set(v___x_241_, 0, v_size_x27_244_);
v___x_255_ = v___x_241_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_size_x27_244_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_val_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v___x_258_; 
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 1, v_buckets_x27_246_);
lean_ctor_set(v___x_241_, 0, v_size_x27_244_);
v___x_258_ = v___x_241_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_size_x27_244_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_buckets_x27_246_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_dec(v_b_221_);
lean_dec(v_a_220_);
return v_m_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(lean_object* v_f_265_, lean_object* v_as_266_, size_t v_i_267_, size_t v_stop_268_, lean_object* v_b_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_usize_dec_eq(v_i_267_, v_stop_268_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_array_uget_borrowed(v_as_266_, v_i_267_);
lean_inc_ref(v_f_265_);
lean_inc_ref(v___y_270_);
lean_inc(v___x_273_);
v___x_274_ = lean_apply_3(v_f_265_, v___x_273_, v___y_270_, v___y_271_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_dec_ref(v_f_265_);
return v___x_274_;
}
else
{
lean_object* v_a_275_; lean_object* v_fst_276_; lean_object* v_snd_277_; size_t v___x_278_; size_t v___x_279_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_274_, 1);
v_fst_276_ = lean_ctor_get(v_a_275_, 0);
lean_inc(v_fst_276_);
v_snd_277_ = lean_ctor_get(v_a_275_, 1);
lean_inc(v_snd_277_);
lean_dec(v_a_275_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_add(v_i_267_, v___x_278_);
v_i_267_ = v___x_279_;
v_b_269_ = v_fst_276_;
v___y_271_ = v_snd_277_;
goto _start;
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v_f_265_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_b_269_);
lean_ctor_set(v___x_281_, 1, v___y_271_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed(lean_object* v_f_283_, lean_object* v_as_284_, lean_object* v_i_285_, lean_object* v_stop_286_, lean_object* v_b_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
size_t v_i_boxed_290_; size_t v_stop_boxed_291_; lean_object* v_res_292_; 
v_i_boxed_290_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_stop_boxed_291_ = lean_unbox_usize(v_stop_286_);
lean_dec(v_stop_286_);
v_res_292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_283_, v_as_284_, v_i_boxed_290_, v_stop_boxed_291_, v_b_287_, v___y_288_, v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec_ref(v_as_284_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(lean_object* v_f_293_, lean_object* v_as_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
if (lean_obj_tag(v_as_294_) == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_f_293_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___y_296_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v_head_300_; lean_object* v_tail_301_; lean_object* v_ctor_302_; lean_object* v_rhs_303_; lean_object* v___x_304_; 
v_head_300_ = lean_ctor_get(v_as_294_, 0);
lean_inc(v_head_300_);
v_tail_301_ = lean_ctor_get(v_as_294_, 1);
lean_inc(v_tail_301_);
lean_dec_ref_known(v_as_294_, 2);
v_ctor_302_ = lean_ctor_get(v_head_300_, 0);
lean_inc(v_ctor_302_);
v_rhs_303_ = lean_ctor_get(v_head_300_, 2);
lean_inc_ref(v_rhs_303_);
lean_dec(v_head_300_);
lean_inc_ref(v_f_293_);
lean_inc_ref(v___y_295_);
v___x_304_ = lean_apply_3(v_f_293_, v_ctor_302_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_dec_ref(v_rhs_303_);
lean_dec(v_tail_301_);
lean_dec_ref(v_f_293_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v_snd_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v_snd_306_ = lean_ctor_get(v_a_305_, 1);
lean_inc(v_snd_306_);
lean_dec(v_a_305_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = l_Lean_Expr_getUsedConstants(v_rhs_303_);
v___x_309_ = lean_array_get_size(v___x_308_);
v___x_310_ = lean_nat_dec_lt(v___x_307_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec_ref(v___x_308_);
v_as_294_ = v_tail_301_;
v___y_296_ = v_snd_306_;
goto _start;
}
else
{
lean_object* v___x_312_; size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_box(0);
v___x_313_ = ((size_t)0ULL);
v___x_314_ = lean_usize_of_nat(v___x_309_);
lean_inc_ref(v_f_293_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_293_, v___x_308_, v___x_313_, v___x_314_, v___x_312_, v___y_295_, v_snd_306_);
lean_dec_ref(v___x_308_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_dec(v_tail_301_);
lean_dec_ref(v_f_293_);
return v___x_315_;
}
else
{
lean_object* v_a_316_; lean_object* v_snd_317_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref_known(v___x_315_, 1);
v_snd_317_ = lean_ctor_get(v_a_316_, 1);
lean_inc(v_snd_317_);
lean_dec(v_a_316_);
v_as_294_ = v_tail_301_;
v___y_296_ = v_snd_317_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2___boxed(lean_object* v_f_319_, lean_object* v_as_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(v_f_319_, v_as_320_, v___y_321_, v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(lean_object* v_f_324_, lean_object* v_as_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
if (lean_obj_tag(v_as_325_) == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_f_324_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___y_327_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
else
{
lean_object* v_head_331_; lean_object* v_tail_332_; lean_object* v___x_333_; 
v_head_331_ = lean_ctor_get(v_as_325_, 0);
lean_inc(v_head_331_);
v_tail_332_ = lean_ctor_get(v_as_325_, 1);
lean_inc(v_tail_332_);
lean_dec_ref_known(v_as_325_, 2);
lean_inc_ref(v_f_324_);
lean_inc_ref(v___y_326_);
v___x_333_ = lean_apply_3(v_f_324_, v_head_331_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_dec(v_tail_332_);
lean_dec_ref(v_f_324_);
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v_snd_335_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v_snd_335_ = lean_ctor_get(v_a_334_, 1);
lean_inc(v_snd_335_);
lean_dec(v_a_334_);
v_as_325_ = v_tail_332_;
v___y_327_ = v_snd_335_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1___boxed(lean_object* v_f_337_, lean_object* v_as_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_337_, v_as_338_, v___y_339_, v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(lean_object* v___x_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_342_);
lean_ctor_set(v___x_345_, 1, v___y_344_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0___boxed(lean_object* v___x_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(v___x_347_, v___y_348_, v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(lean_object* v_info_355_, lean_object* v_f_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___y_382_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_378_ = l_Lean_ConstantInfo_type(v_info_355_);
v___x_379_ = l_Lean_Expr_getUsedConstants(v___x_378_);
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_array_get_size(v___x_379_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_nat_dec_lt(v___x_380_, v___x_402_);
if (v___x_404_ == 0)
{
lean_object* v___f_405_; 
lean_dec_ref(v___x_379_);
v___f_405_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___closed__0));
v___y_382_ = v___f_405_;
goto v___jp_381_;
}
else
{
size_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = lean_usize_of_nat(v___x_402_);
v___x_407_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1));
v___x_408_ = lean_box_usize(v___x_406_);
lean_inc_ref(v_f_356_);
v___x_409_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed), 7, 5);
lean_closure_set(v___x_409_, 0, v_f_356_);
lean_closure_set(v___x_409_, 1, v___x_379_);
lean_closure_set(v___x_409_, 2, v___x_407_);
lean_closure_set(v___x_409_, 3, v___x_408_);
lean_closure_set(v___x_409_, 4, v___x_403_);
v___y_382_ = v___x_409_;
goto v___jp_381_;
}
v___jp_359_:
{
switch(lean_obj_tag(v_info_355_))
{
case 5:
{
lean_object* v_val_362_; lean_object* v_all_363_; lean_object* v_ctors_364_; lean_object* v___x_365_; 
v_val_362_ = lean_ctor_get(v_info_355_, 0);
lean_inc_ref(v_val_362_);
lean_dec_ref_known(v_info_355_, 1);
v_all_363_ = lean_ctor_get(v_val_362_, 3);
lean_inc(v_all_363_);
v_ctors_364_ = lean_ctor_get(v_val_362_, 4);
lean_inc(v_ctors_364_);
lean_dec_ref(v_val_362_);
lean_inc_ref(v_f_356_);
v___x_365_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_356_, v_ctors_364_, v___y_360_, v___y_361_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_dec(v_all_363_);
lean_dec_ref(v_f_356_);
return v___x_365_;
}
else
{
lean_object* v_a_366_; lean_object* v_snd_367_; lean_object* v___x_368_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_365_, 1);
v_snd_367_ = lean_ctor_get(v_a_366_, 1);
lean_inc(v_snd_367_);
lean_dec(v_a_366_);
v___x_368_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_356_, v_all_363_, v___y_360_, v_snd_367_);
return v___x_368_;
}
}
case 6:
{
lean_object* v_val_369_; lean_object* v_induct_370_; lean_object* v___x_371_; 
v_val_369_ = lean_ctor_get(v_info_355_, 0);
lean_inc_ref(v_val_369_);
lean_dec_ref_known(v_info_355_, 1);
v_induct_370_ = lean_ctor_get(v_val_369_, 1);
lean_inc(v_induct_370_);
lean_dec_ref(v_val_369_);
lean_inc_ref(v___y_360_);
v___x_371_ = lean_apply_3(v_f_356_, v_induct_370_, v___y_360_, v___y_361_);
return v___x_371_;
}
case 7:
{
lean_object* v_val_372_; lean_object* v_rules_373_; lean_object* v___x_374_; 
v_val_372_ = lean_ctor_get(v_info_355_, 0);
lean_inc_ref(v_val_372_);
lean_dec_ref_known(v_info_355_, 1);
v_rules_373_ = lean_ctor_get(v_val_372_, 6);
lean_inc(v_rules_373_);
lean_dec_ref(v_val_372_);
v___x_374_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(v_f_356_, v_rules_373_, v___y_360_, v___y_361_);
return v___x_374_;
}
default: 
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v_f_356_);
lean_dec_ref(v_info_355_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___y_361_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
v___jp_381_:
{
lean_object* v___x_383_; 
lean_inc_ref(v___y_357_);
v___x_383_ = lean_apply_2(v___y_382_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_dec_ref(v_f_356_);
lean_dec_ref(v_info_355_);
return v___x_383_;
}
else
{
lean_object* v_a_384_; lean_object* v_snd_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v_snd_385_ = lean_ctor_get(v_a_384_, 1);
lean_inc(v_snd_385_);
lean_dec(v_a_384_);
v___x_386_ = l_Lean_ConstantInfo_name(v_info_355_);
lean_inc_ref(v_f_356_);
lean_inc_ref(v___y_357_);
v___x_387_ = lean_apply_3(v_f_356_, v___x_386_, v___y_357_, v_snd_385_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_dec_ref(v_f_356_);
lean_dec_ref(v_info_355_);
return v___x_387_;
}
else
{
lean_object* v_a_388_; lean_object* v_snd_389_; uint8_t v___x_390_; lean_object* v___x_391_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref_known(v___x_387_, 1);
v_snd_389_ = lean_ctor_get(v_a_388_, 1);
lean_inc(v_snd_389_);
lean_dec(v_a_388_);
v___x_390_ = 1;
lean_inc_ref(v_info_355_);
v___x_391_ = l_Lean_ConstantInfo_value_x3f(v_info_355_, v___x_390_);
if (lean_obj_tag(v___x_391_) == 1)
{
lean_object* v_val_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_val_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = l_Lean_Expr_getUsedConstants(v_val_392_);
v___x_394_ = lean_array_get_size(v___x_393_);
v___x_395_ = lean_nat_dec_lt(v___x_380_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec_ref(v___x_393_);
v___y_360_ = v___y_357_;
v___y_361_ = v_snd_389_;
goto v___jp_359_;
}
else
{
lean_object* v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_394_);
lean_inc_ref(v_f_356_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_356_, v___x_393_, v___x_397_, v___x_398_, v___x_396_, v___y_357_, v_snd_389_);
lean_dec_ref(v___x_393_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_dec_ref(v_f_356_);
lean_dec_ref(v_info_355_);
return v___x_399_;
}
else
{
lean_object* v_a_400_; lean_object* v_snd_401_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v___x_399_, 1);
v_snd_401_ = lean_ctor_get(v_a_400_, 1);
lean_inc(v_snd_401_);
lean_dec(v_a_400_);
v___y_360_ = v___y_357_;
v___y_361_ = v_snd_401_;
goto v___jp_359_;
}
}
}
else
{
lean_dec(v___x_391_);
v___y_360_ = v___y_357_;
v___y_361_ = v_snd_389_;
goto v___jp_359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed(lean_object* v_info_410_, lean_object* v_f_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(v_info_410_, v_f_411_, v___y_412_, v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_worklist_418_; lean_object* v_checked_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_worklist_418_ = lean_ctor_get(v_a_417_, 0);
v_checked_419_ = lean_ctor_get(v_a_417_, 1);
v___x_420_ = lean_array_get_size(v_worklist_418_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_nat_dec_eq(v___x_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_463_; 
lean_inc_ref(v_checked_419_);
lean_inc_ref(v_worklist_418_);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; lean_object* v_unused_465_; 
v_unused_464_ = lean_ctor_get(v_a_417_, 1);
lean_dec(v_unused_464_);
v_unused_465_ = lean_ctor_get(v_a_417_, 0);
lean_dec(v_unused_465_);
v___x_424_ = v_a_417_;
v_isShared_425_ = v_isSharedCheck_463_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_a_417_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_463_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_426_ = lean_box(0);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_sub(v___x_420_, v___x_427_);
v___x_429_ = lean_array_get(v___x_426_, v_worklist_418_, v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = lean_array_pop(v_worklist_418_);
lean_inc_ref(v_checked_419_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_430_);
v___x_432_ = v___x_424_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_checked_419_);
v___x_432_ = v_reuseFailAlloc_462_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
uint8_t v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_checked_419_, v___x_429_);
lean_dec_ref(v_checked_419_);
if (v___x_433_ == 0)
{
lean_object* v_solution_434_; lean_object* v_constMap_435_; lean_object* v___x_436_; 
v_solution_434_ = lean_ctor_get(v_a_416_, 0);
v_constMap_435_ = lean_ctor_get(v_solution_434_, 0);
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_435_, v___x_429_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v_val_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___closed__0));
v___x_439_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(v_val_437_, v___x_438_, v_a_416_, v___x_432_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_dec(v___x_429_);
return v___x_439_;
}
else
{
lean_object* v_a_440_; lean_object* v_snd_441_; lean_object* v_worklist_442_; lean_object* v_checked_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v_snd_441_ = lean_ctor_get(v_a_440_, 1);
lean_inc(v_snd_441_);
lean_dec(v_a_440_);
v_worklist_442_ = lean_ctor_get(v_snd_441_, 0);
v_checked_443_ = lean_ctor_get(v_snd_441_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_snd_441_);
if (v_isSharedCheck_453_ == 0)
{
v___x_445_ = v_snd_441_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_checked_443_);
lean_inc(v_worklist_442_);
lean_dec(v_snd_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_447_ = lean_box(0);
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_checked_443_, v___x_429_, v___x_447_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_448_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_worklist_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_417_ = v___x_450_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v___x_436_);
lean_dec_ref(v___x_432_);
v___x_454_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2));
v___x_455_ = 1;
v___x_456_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_429_, v___x_455_);
v___x_457_ = lean_string_append(v___x_454_, v___x_456_);
lean_dec_ref(v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
else
{
lean_dec(v___x_429_);
v_a_417_ = v___x_432_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_417_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___boxed(lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v_a_469_, v_a_470_);
lean_dec_ref(v_a_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1(lean_object* v_00_u03b2_472_, lean_object* v_m_473_, lean_object* v_a_474_, lean_object* v_b_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_m_473_, v_a_474_, v_b_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4(lean_object* v_00_u03b2_477_, lean_object* v_data_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_data_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_480_, lean_object* v_i_481_, lean_object* v_source_482_, lean_object* v_target_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(v_i_481_, v_source_482_, v_target_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(v_x_486_, v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(lean_object* v_f_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_, lean_object* v_b_493_, lean_object* v___y_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; size_t v___x_500_; size_t v___x_501_; 
v___x_496_ = lean_array_uget_borrowed(v_as_490_, v_i_491_);
lean_inc_ref(v_f_489_);
lean_inc(v___x_496_);
v___x_497_ = lean_apply_2(v_f_489_, v___x_496_, v___y_494_);
v_fst_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_snd_499_);
lean_dec_ref(v___x_497_);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_491_, v___x_500_);
v_i_491_ = v___x_501_;
v_b_493_ = v_fst_498_;
v___y_494_ = v_snd_499_;
goto _start;
}
else
{
lean_object* v___x_503_; 
lean_dec_ref(v_f_489_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_b_493_);
lean_ctor_set(v___x_503_, 1, v___y_494_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed(lean_object* v_f_504_, lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_stop_507_, lean_object* v_b_508_, lean_object* v___y_509_){
_start:
{
size_t v_i_boxed_510_; size_t v_stop_boxed_511_; lean_object* v_res_512_; 
v_i_boxed_510_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_stop_boxed_511_ = lean_unbox_usize(v_stop_507_);
lean_dec(v_stop_507_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_504_, v_as_505_, v_i_boxed_510_, v_stop_boxed_511_, v_b_508_, v___y_509_);
lean_dec_ref(v_as_505_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(lean_object* v_f_513_, lean_object* v_as_514_, lean_object* v___y_515_){
_start:
{
if (lean_obj_tag(v_as_514_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v_f_513_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___y_515_);
return v___x_517_;
}
else
{
lean_object* v_head_518_; lean_object* v_tail_519_; lean_object* v_ctor_520_; lean_object* v_rhs_521_; lean_object* v___x_522_; lean_object* v_snd_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_head_518_ = lean_ctor_get(v_as_514_, 0);
lean_inc(v_head_518_);
v_tail_519_ = lean_ctor_get(v_as_514_, 1);
lean_inc(v_tail_519_);
lean_dec_ref_known(v_as_514_, 2);
v_ctor_520_ = lean_ctor_get(v_head_518_, 0);
lean_inc(v_ctor_520_);
v_rhs_521_ = lean_ctor_get(v_head_518_, 2);
lean_inc_ref(v_rhs_521_);
lean_dec(v_head_518_);
lean_inc_ref(v_f_513_);
v___x_522_ = lean_apply_2(v_f_513_, v_ctor_520_, v___y_515_);
v_snd_523_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_snd_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_Expr_getUsedConstants(v_rhs_521_);
v___x_526_ = lean_array_get_size(v___x_525_);
v___x_527_ = lean_nat_dec_lt(v___x_524_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec_ref(v___x_525_);
v_as_514_ = v_tail_519_;
v___y_515_ = v_snd_523_;
goto _start;
}
else
{
lean_object* v___x_529_; size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; lean_object* v_snd_533_; 
v___x_529_ = lean_box(0);
v___x_530_ = ((size_t)0ULL);
v___x_531_ = lean_usize_of_nat(v___x_526_);
lean_inc_ref(v_f_513_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_513_, v___x_525_, v___x_530_, v___x_531_, v___x_529_, v_snd_523_);
lean_dec_ref(v___x_525_);
v_snd_533_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_532_);
v_as_514_ = v_tail_519_;
v___y_515_ = v_snd_533_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(lean_object* v_f_535_, lean_object* v_as_536_, lean_object* v___y_537_){
_start:
{
if (lean_obj_tag(v_as_536_) == 0)
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref(v_f_535_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___y_537_);
return v___x_539_;
}
else
{
lean_object* v_head_540_; lean_object* v_tail_541_; lean_object* v___x_542_; lean_object* v_snd_543_; 
v_head_540_ = lean_ctor_get(v_as_536_, 0);
lean_inc(v_head_540_);
v_tail_541_ = lean_ctor_get(v_as_536_, 1);
lean_inc(v_tail_541_);
lean_dec_ref_known(v_as_536_, 2);
lean_inc_ref(v_f_535_);
v___x_542_ = lean_apply_2(v_f_535_, v_head_540_, v___y_537_);
v_snd_543_ = lean_ctor_get(v___x_542_, 1);
lean_inc(v_snd_543_);
lean_dec_ref(v___x_542_);
v_as_536_ = v_tail_541_;
v___y_537_ = v_snd_543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___lam__0(lean_object* v___x_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___y_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(lean_object* v_info_550_, lean_object* v_f_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___y_554_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___y_573_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_569_ = l_Lean_ConstantInfo_type(v_info_550_);
v___x_570_ = l_Lean_Expr_getUsedConstants(v___x_569_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_array_get_size(v___x_570_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_nat_dec_lt(v___x_571_, v___x_590_);
if (v___x_592_ == 0)
{
lean_object* v___f_593_; 
lean_dec_ref(v___x_570_);
v___f_593_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___closed__0));
v___y_573_ = v___f_593_;
goto v___jp_572_;
}
else
{
size_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_usize_of_nat(v___x_590_);
v___x_595_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1));
v___x_596_ = lean_box_usize(v___x_594_);
lean_inc_ref(v_f_551_);
v___x_597_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed), 6, 5);
lean_closure_set(v___x_597_, 0, v_f_551_);
lean_closure_set(v___x_597_, 1, v___x_570_);
lean_closure_set(v___x_597_, 2, v___x_595_);
lean_closure_set(v___x_597_, 3, v___x_596_);
lean_closure_set(v___x_597_, 4, v___x_591_);
v___y_573_ = v___x_597_;
goto v___jp_572_;
}
v___jp_553_:
{
switch(lean_obj_tag(v_info_550_))
{
case 5:
{
lean_object* v_val_555_; lean_object* v_all_556_; lean_object* v_ctors_557_; lean_object* v___x_558_; lean_object* v_snd_559_; lean_object* v___x_560_; 
v_val_555_ = lean_ctor_get(v_info_550_, 0);
lean_inc_ref(v_val_555_);
lean_dec_ref_known(v_info_550_, 1);
v_all_556_ = lean_ctor_get(v_val_555_, 3);
lean_inc(v_all_556_);
v_ctors_557_ = lean_ctor_get(v_val_555_, 4);
lean_inc(v_ctors_557_);
lean_dec_ref(v_val_555_);
lean_inc_ref(v_f_551_);
v___x_558_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(v_f_551_, v_ctors_557_, v___y_554_);
v_snd_559_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(v_f_551_, v_all_556_, v_snd_559_);
return v___x_560_;
}
case 6:
{
lean_object* v_val_561_; lean_object* v_induct_562_; lean_object* v___x_563_; 
v_val_561_ = lean_ctor_get(v_info_550_, 0);
lean_inc_ref(v_val_561_);
lean_dec_ref_known(v_info_550_, 1);
v_induct_562_ = lean_ctor_get(v_val_561_, 1);
lean_inc(v_induct_562_);
lean_dec_ref(v_val_561_);
v___x_563_ = lean_apply_2(v_f_551_, v_induct_562_, v___y_554_);
return v___x_563_;
}
case 7:
{
lean_object* v_val_564_; lean_object* v_rules_565_; lean_object* v___x_566_; 
v_val_564_ = lean_ctor_get(v_info_550_, 0);
lean_inc_ref(v_val_564_);
lean_dec_ref_known(v_info_550_, 1);
v_rules_565_ = lean_ctor_get(v_val_564_, 6);
lean_inc(v_rules_565_);
lean_dec_ref(v_val_564_);
v___x_566_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(v_f_551_, v_rules_565_, v___y_554_);
return v___x_566_;
}
default: 
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v_f_551_);
lean_dec_ref(v_info_550_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___y_554_);
return v___x_568_;
}
}
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v_snd_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_snd_578_; uint8_t v___x_579_; lean_object* v___x_580_; 
v___x_574_ = lean_apply_1(v___y_573_, v___y_552_);
v_snd_575_ = lean_ctor_get(v___x_574_, 1);
lean_inc(v_snd_575_);
lean_dec_ref(v___x_574_);
v___x_576_ = l_Lean_ConstantInfo_name(v_info_550_);
lean_inc_ref(v_f_551_);
v___x_577_ = lean_apply_2(v_f_551_, v___x_576_, v_snd_575_);
v_snd_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_snd_578_);
lean_dec_ref(v___x_577_);
v___x_579_ = 1;
lean_inc_ref(v_info_550_);
v___x_580_ = l_Lean_ConstantInfo_value_x3f(v_info_550_, v___x_579_);
if (lean_obj_tag(v___x_580_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = l_Lean_Expr_getUsedConstants(v_val_581_);
v___x_583_ = lean_array_get_size(v___x_582_);
v___x_584_ = lean_nat_dec_lt(v___x_571_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec_ref(v___x_582_);
v___y_554_ = v_snd_578_;
goto v___jp_553_;
}
else
{
lean_object* v___x_585_; size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; lean_object* v_snd_589_; 
v___x_585_ = lean_box(0);
v___x_586_ = ((size_t)0ULL);
v___x_587_ = lean_usize_of_nat(v___x_583_);
lean_inc_ref(v_f_551_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_551_, v___x_582_, v___x_586_, v___x_587_, v___x_585_, v_snd_578_);
lean_dec_ref(v___x_582_);
v_snd_589_ = lean_ctor_get(v___x_588_, 1);
lean_inc(v_snd_589_);
lean_dec_ref(v___x_588_);
v___y_554_ = v_snd_589_;
goto v___jp_553_;
}
}
else
{
lean_dec(v___x_580_);
v___y_554_ = v_snd_578_;
goto v___jp_553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(lean_object* v_a_598_, lean_object* v_constMap_599_, lean_object* v___x_600_, lean_object* v_ref_601_, lean_object* v___y_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_name_eq(v_ref_601_, v_a_598_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_599_, v_ref_601_);
if (lean_obj_tag(v___x_604_) == 1)
{
lean_object* v_val_605_; 
v_val_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_604_, 1);
if (lean_obj_tag(v_val_605_) == 0)
{
lean_object* v_fst_606_; lean_object* v_snd_607_; uint8_t v___x_608_; 
lean_dec_ref_known(v_val_605_, 1);
v_fst_606_ = lean_ctor_get(v___y_602_, 0);
v_snd_607_ = lean_ctor_get(v___y_602_, 1);
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_fst_606_, v_ref_601_);
if (v___x_608_ == 0)
{
lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_619_; 
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
v_isSharedCheck_619_ = !lean_is_exclusive(v___y_602_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; lean_object* v_unused_621_; 
v_unused_620_ = lean_ctor_get(v___y_602_, 1);
lean_dec(v_unused_620_);
v_unused_621_ = lean_ctor_get(v___y_602_, 0);
lean_dec(v_unused_621_);
v___x_610_ = v___y_602_;
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
else
{
lean_dec(v___y_602_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
lean_inc(v_ref_601_);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_fst_606_, v_ref_601_, v___x_600_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v_a_598_);
lean_ctor_set(v___x_610_, 0, v_ref_601_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_ref_601_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_a_598_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_array_push(v_snd_607_, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_612_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_600_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
return v___x_617_;
}
}
}
else
{
lean_object* v___x_622_; 
lean_dec(v_ref_601_);
lean_dec(v_a_598_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_600_);
lean_ctor_set(v___x_622_, 1, v___y_602_);
return v___x_622_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_val_605_);
lean_dec(v_ref_601_);
lean_dec(v_a_598_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_600_);
lean_ctor_set(v___x_623_, 1, v___y_602_);
return v___x_623_;
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v___x_604_);
lean_dec(v_ref_601_);
lean_dec(v_a_598_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_600_);
lean_ctor_set(v___x_624_, 1, v___y_602_);
return v___x_624_;
}
}
else
{
lean_object* v___x_625_; 
lean_dec(v_ref_601_);
lean_dec(v_a_598_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_600_);
lean_ctor_set(v___x_625_, 1, v___y_602_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed(lean_object* v_a_626_, lean_object* v_constMap_627_, lean_object* v___x_628_, lean_object* v_ref_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(v_a_626_, v_constMap_627_, v___x_628_, v_ref_629_, v___y_630_);
lean_dec_ref(v_constMap_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(lean_object* v_env_632_, lean_object* v_as_633_, size_t v_sz_634_, size_t v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_a_639_; lean_object* v_snd_640_; uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_lt(v_i_635_, v_sz_634_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_env_632_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_b_636_);
lean_ctor_set(v___x_645_, 1, v___y_637_);
return v___x_645_;
}
else
{
lean_object* v_constMap_646_; lean_object* v___x_647_; lean_object* v_a_648_; lean_object* v___x_649_; 
v_constMap_646_ = lean_ctor_get(v_env_632_, 0);
v___x_647_ = lean_box(0);
v_a_648_ = lean_array_uget_borrowed(v_as_633_, v_i_635_);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_646_, v_a_648_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_val_650_; lean_object* v___f_651_; lean_object* v___x_652_; lean_object* v_snd_653_; 
v_val_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_val_650_);
lean_dec_ref_known(v___x_649_, 1);
lean_inc_ref(v_constMap_646_);
lean_inc(v_a_648_);
v___f_651_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_651_, 0, v_a_648_);
lean_closure_set(v___f_651_, 1, v_constMap_646_);
lean_closure_set(v___f_651_, 2, v___x_647_);
v___x_652_ = l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(v_val_650_, v___f_651_, v___y_637_);
v_snd_653_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_snd_653_);
lean_dec_ref(v___x_652_);
v_a_639_ = v___x_647_;
v_snd_640_ = v_snd_653_;
goto v___jp_638_;
}
else
{
lean_dec(v___x_649_);
v_a_639_ = v___x_647_;
v_snd_640_ = v___y_637_;
goto v___jp_638_;
}
}
v___jp_638_:
{
size_t v___x_641_; size_t v___x_642_; 
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_i_635_, v___x_641_);
v_i_635_ = v___x_642_;
v_b_636_ = v_a_639_;
v___y_637_ = v_snd_640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___boxed(lean_object* v_env_654_, lean_object* v_as_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_b_658_, lean_object* v___y_659_){
_start:
{
size_t v_sz_boxed_660_; size_t v_i_boxed_661_; lean_object* v_res_662_; 
v_sz_boxed_660_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_661_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_654_, v_as_655_, v_sz_boxed_660_, v_i_boxed_661_, v_b_658_, v___y_659_);
lean_dec_ref(v_as_655_);
return v_res_662_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__0(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_unsigned_to_nat(16u);
v___x_665_ = lean_mk_array(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__1(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__0, &l_Lake_Check_usedAxioms___closed__0_once, _init_l_Lake_Check_usedAxioms___closed__0);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l_Lake_Check_usedAxioms___closed__2));
v___x_672_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_usedAxioms(lean_object* v_env_674_){
_start:
{
lean_object* v_constOrder_675_; lean_object* v___x_676_; size_t v_sz_677_; size_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_snd_681_; lean_object* v_snd_682_; 
v_constOrder_675_ = lean_ctor_get(v_env_674_, 1);
lean_inc_ref(v_constOrder_675_);
v___x_676_ = lean_box(0);
v_sz_677_ = lean_array_size(v_constOrder_675_);
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__3, &l_Lake_Check_usedAxioms___closed__3_once, _init_l_Lake_Check_usedAxioms___closed__3);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_674_, v_constOrder_675_, v_sz_677_, v___x_678_, v___x_676_, v___x_679_);
lean_dec_ref(v_constOrder_675_);
v_snd_681_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_snd_681_);
lean_dec_ref(v___x_680_);
v_snd_682_ = lean_ctor_get(v_snd_681_, 1);
lean_inc(v_snd_682_);
lean_dec(v_snd_681_);
return v_snd_682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(lean_object* v_as_683_, size_t v_sz_684_, size_t v_i_685_, lean_object* v_b_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_685_, v_sz_684_);
if (v___x_687_ == 0)
{
return v_b_686_;
}
else
{
lean_object* v_a_688_; lean_object* v___x_689_; lean_object* v_r_690_; size_t v___x_691_; size_t v___x_692_; 
v_a_688_ = lean_array_uget_borrowed(v_as_683_, v_i_685_);
v___x_689_ = lean_box(0);
lean_inc(v_a_688_);
v_r_690_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_b_686_, v_a_688_, v___x_689_);
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_685_, v___x_691_);
v_i_685_ = v___x_692_;
v_b_686_ = v_r_690_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2___boxed(lean_object* v_as_694_, lean_object* v_sz_695_, lean_object* v_i_696_, lean_object* v_b_697_){
_start:
{
size_t v_sz_boxed_698_; size_t v_i_boxed_699_; lean_object* v_res_700_; 
v_sz_boxed_698_ = lean_unbox_usize(v_sz_695_);
lean_dec(v_sz_695_);
v_i_boxed_699_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_as_694_, v_sz_boxed_698_, v_i_boxed_699_, v_b_697_);
lean_dec_ref(v_as_694_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(lean_object* v_m_701_, lean_object* v_l_702_){
_start:
{
size_t v_sz_703_; size_t v___x_704_; lean_object* v___x_705_; 
v_sz_703_ = lean_array_size(v_l_702_);
v___x_704_ = ((size_t)0ULL);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_l_702_, v_sz_703_, v___x_704_, v_m_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2___boxed(lean_object* v_m_706_, lean_object* v_l_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v_m_706_, v_l_707_);
lean_dec_ref(v_l_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(lean_object* v_solution_711_, lean_object* v_as_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_b_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v_b_715_);
return v___x_717_;
}
else
{
lean_object* v_constMap_718_; lean_object* v_a_719_; lean_object* v___x_720_; 
v_constMap_718_ = lean_ctor_get(v_solution_711_, 0);
v_a_719_ = lean_array_uget_borrowed(v_as_712_, v_i_714_);
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_718_, v_a_719_);
if (lean_obj_tag(v___x_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_740_; 
v_val_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_740_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_740_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_val_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_740_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
if (lean_obj_tag(v_val_721_) == 2)
{
lean_object* v_val_725_; lean_object* v_toConstantVal_726_; lean_object* v_name_727_; lean_object* v___x_728_; size_t v___x_729_; size_t v___x_730_; 
lean_del_object(v___x_723_);
v_val_725_ = lean_ctor_get(v_val_721_, 0);
lean_inc_ref(v_val_725_);
lean_dec_ref_known(v_val_721_, 1);
v_toConstantVal_726_ = lean_ctor_get(v_val_725_, 0);
lean_inc_ref(v_toConstantVal_726_);
lean_dec_ref(v_val_725_);
v_name_727_ = lean_ctor_get(v_toConstantVal_726_, 0);
lean_inc(v_name_727_);
lean_dec_ref(v_toConstantVal_726_);
v___x_728_ = lean_array_push(v_b_715_, v_name_727_);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_714_, v___x_729_);
v_i_714_ = v___x_730_;
v_b_715_ = v___x_728_;
goto _start;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec(v_val_721_);
lean_dec_ref(v_b_715_);
v___x_732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0));
lean_inc(v_a_719_);
v___x_733_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_719_, v___x_716_);
v___x_734_ = lean_string_append(v___x_732_, v___x_733_);
lean_dec_ref(v___x_733_);
v___x_735_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_736_ = lean_string_append(v___x_734_, v___x_735_);
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 0);
lean_ctor_set(v___x_723_, 0, v___x_736_);
v___x_738_ = v___x_723_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v___x_720_);
lean_dec_ref(v_b_715_);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_719_);
v___x_742_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_719_, v___x_716_);
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
lean_dec_ref(v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___boxed(lean_object* v_solution_747_, lean_object* v_as_748_, lean_object* v_sz_749_, lean_object* v_i_750_, lean_object* v_b_751_){
_start:
{
size_t v_sz_boxed_752_; size_t v_i_boxed_753_; lean_object* v_res_754_; 
v_sz_boxed_752_ = lean_unbox_usize(v_sz_749_);
lean_dec(v_sz_749_);
v_i_boxed_753_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_res_754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_747_, v_as_748_, v_sz_boxed_752_, v_i_boxed_753_, v_b_751_);
lean_dec_ref(v_as_748_);
lean_dec_ref(v_solution_747_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(lean_object* v_solution_756_, lean_object* v_as_757_, size_t v_sz_758_, size_t v_i_759_, lean_object* v_b_760_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = lean_usize_dec_lt(v_i_759_, v_sz_758_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_b_760_);
return v___x_762_;
}
else
{
lean_object* v_constMap_763_; lean_object* v_a_764_; lean_object* v___x_765_; 
v_constMap_763_ = lean_ctor_get(v_solution_756_, 0);
v_a_764_ = lean_array_uget_borrowed(v_as_757_, v_i_759_);
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_763_, v_a_764_);
if (lean_obj_tag(v___x_765_) == 1)
{
lean_object* v_val_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_785_; 
v_val_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_785_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_785_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_val_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_785_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
if (lean_obj_tag(v_val_766_) == 1)
{
lean_object* v_val_770_; lean_object* v_toConstantVal_771_; lean_object* v_name_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; 
lean_del_object(v___x_768_);
v_val_770_ = lean_ctor_get(v_val_766_, 0);
lean_inc_ref(v_val_770_);
lean_dec_ref_known(v_val_766_, 1);
v_toConstantVal_771_ = lean_ctor_get(v_val_770_, 0);
lean_inc_ref(v_toConstantVal_771_);
lean_dec_ref(v_val_770_);
v_name_772_ = lean_ctor_get(v_toConstantVal_771_, 0);
lean_inc(v_name_772_);
lean_dec_ref(v_toConstantVal_771_);
v___x_773_ = lean_array_push(v_b_760_, v_name_772_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_759_, v___x_774_);
v_i_759_ = v___x_775_;
v_b_760_ = v___x_773_;
goto _start;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_val_766_);
lean_dec_ref(v_b_760_);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0));
lean_inc(v_a_764_);
v___x_778_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_764_, v___x_761_);
v___x_779_ = lean_string_append(v___x_777_, v___x_778_);
lean_dec_ref(v___x_778_);
v___x_780_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 0);
lean_ctor_set(v___x_768_, 0, v___x_781_);
v___x_783_ = v___x_768_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec(v___x_765_);
lean_dec_ref(v_b_760_);
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_764_);
v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_764_, v___x_761_);
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
lean_dec_ref(v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___boxed(lean_object* v_solution_792_, lean_object* v_as_793_, lean_object* v_sz_794_, lean_object* v_i_795_, lean_object* v_b_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_794_);
lean_dec(v_sz_794_);
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_792_, v_as_793_, v_sz_boxed_797_, v_i_boxed_798_, v_b_796_);
lean_dec_ref(v_as_793_);
lean_dec_ref(v_solution_792_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms(lean_object* v_solution_802_, lean_object* v_theoremTargets_803_, lean_object* v_definitionTargets_804_, lean_object* v_legalAxioms_805_){
_start:
{
lean_object* v_worklist_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; 
v_worklist_806_ = ((lean_object*)(l_Lake_Check_checkAxioms___closed__0));
v_sz_807_ = lean_array_size(v_theoremTargets_803_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_802_, v_theoremTargets_803_, v_sz_807_, v___x_808_, v_worklist_806_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_solution_802_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; size_t v_sz_819_; lean_object* v___x_820_; 
v_a_818_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_809_, 1);
v_sz_819_ = lean_array_size(v_definitionTargets_804_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_802_, v_definitionTargets_804_, v_sz_819_, v___x_808_, v_a_818_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v_solution_802_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_829_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_820_, 1);
v___x_830_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v___x_830_, v_legalAxioms_805_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_solution_802_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_a_829_);
lean_ctor_set(v___x_833_, 1, v___x_830_);
v___x_834_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v___x_832_, v___x_833_);
lean_dec_ref_known(v___x_832_, 2);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_a_843_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_851_ == 0)
{
v___x_845_ = v___x_834_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_834_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_fst_847_; lean_object* v___x_849_; 
v_fst_847_ = lean_ctor_get(v_a_843_, 0);
lean_inc(v_fst_847_);
lean_dec(v_a_843_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_fst_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms___boxed(lean_object* v_solution_852_, lean_object* v_theoremTargets_853_, lean_object* v_definitionTargets_854_, lean_object* v_legalAxioms_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lake_Check_checkAxioms(v_solution_852_, v_theoremTargets_853_, v_definitionTargets_854_, v_legalAxioms_855_);
lean_dec_ref(v_legalAxioms_855_);
lean_dec_ref(v_definitionTargets_854_);
lean_dec_ref(v_theoremTargets_853_);
return v_res_856_;
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
