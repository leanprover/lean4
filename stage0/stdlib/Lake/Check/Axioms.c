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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(lean_object* v_a_37_, lean_object* v_x_38_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_37_ = stack[0].m_obj;
lean_object* v_x_38_ = stack[1].m_obj;
uint8_t v_res_44_;
v_res_44_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_37_, v_x_38_);
stack->m_num = v_res_44_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg___boxed(lean_object* v_a_45_, lean_object* v_x_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_45_, v_x_46_);
lean_dec(v_x_46_);
lean_dec(v_a_45_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(lean_object* v_m_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_buckets_51_; lean_object* v___x_52_; uint64_t v___y_54_; 
v_buckets_51_ = lean_ctor_get(v_m_49_, 1);
v___x_52_ = lean_array_get_size(v_buckets_51_);
if (lean_obj_tag(v_a_50_) == 0)
{
uint64_t v___x_68_; 
v___x_68_ = 1723ULL;
v___y_54_ = v___x_68_;
goto v___jp_53_;
}
else
{
uint64_t v_hash_69_; 
v_hash_69_ = lean_ctor_get_uint64(v_a_50_, sizeof(void*)*2);
v___y_54_ = v_hash_69_;
goto v___jp_53_;
}
v___jp_53_:
{
uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v_fold_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; size_t v___x_64_; size_t v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_55_ = 32ULL;
v___x_56_ = lean_uint64_shift_right(v___y_54_, v___x_55_);
v_fold_57_ = lean_uint64_xor(v___y_54_, v___x_56_);
v___x_58_ = 16ULL;
v___x_59_ = lean_uint64_shift_right(v_fold_57_, v___x_58_);
v___x_60_ = lean_uint64_xor(v_fold_57_, v___x_59_);
v___x_61_ = lean_uint64_to_usize(v___x_60_);
v___x_62_ = lean_usize_of_nat(v___x_52_);
v___x_63_ = ((size_t)1ULL);
v___x_64_ = lean_usize_sub(v___x_62_, v___x_63_);
v___x_65_ = lean_usize_land(v___x_61_, v___x_64_);
v___x_66_ = lean_array_uget_borrowed(v_buckets_51_, v___x_65_);
v___x_67_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_50_, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_49_ = stack[0].m_obj;
lean_object* v_a_50_ = stack[1].m_obj;
uint8_t v_res_70_;
v_res_70_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_m_49_, v_a_50_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg___boxed(lean_object* v_m_71_, lean_object* v_a_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_m_71_, v_a_72_);
lean_dec(v_a_72_);
lean_dec_ref(v_m_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst(lean_object* v_n_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___y_82_; lean_object* v_solution_102_; lean_object* v_legalAxioms_103_; lean_object* v_constMap_104_; lean_object* v___x_105_; 
v_solution_102_ = lean_ctor_get(v_a_79_, 0);
v_legalAxioms_103_ = lean_ctor_get(v_a_79_, 1);
v_constMap_104_ = lean_ctor_get(v_solution_102_, 0);
v___x_105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_104_, v_n_78_);
if (lean_obj_tag(v___x_105_) == 1)
{
lean_object* v_val_106_; 
v_val_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_val_106_);
lean_dec_ref_known(v___x_105_, 1);
if (lean_obj_tag(v_val_106_) == 0)
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_123_; 
v_val_107_ = lean_ctor_get(v_val_106_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v_val_106_);
if (v_isSharedCheck_123_ == 0)
{
v___x_109_ = v_val_106_;
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v_val_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_123_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_toConstantVal_111_; lean_object* v_name_112_; uint8_t v___x_113_; 
v_toConstantVal_111_ = lean_ctor_get(v_val_107_, 0);
lean_inc_ref(v_toConstantVal_111_);
lean_dec_ref(v_val_107_);
v_name_112_ = lean_ctor_get(v_toConstantVal_111_, 0);
lean_inc(v_name_112_);
lean_dec_ref(v_toConstantVal_111_);
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_legalAxioms_103_, v_name_112_);
lean_dec(v_name_112_);
if (v___x_113_ == 0)
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
lean_dec_ref(v_a_80_);
v___x_114_ = 1;
v___x_115_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__0));
v___x_116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_78_, v___x_114_);
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_118_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_119_ = lean_string_append(v___x_117_, v___x_118_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_119_);
v___x_121_ = v___x_109_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
else
{
lean_del_object(v___x_109_);
v___y_82_ = v_a_80_;
goto v___jp_81_;
}
}
}
else
{
lean_dec(v_val_106_);
v___y_82_ = v_a_80_;
goto v___jp_81_;
}
}
else
{
lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v___x_105_);
lean_dec_ref(v_a_80_);
v___x_124_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2));
v___x_125_ = 1;
v___x_126_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_78_, v___x_125_);
v___x_127_ = lean_string_append(v___x_124_, v___x_126_);
lean_dec_ref(v___x_126_);
v___x_128_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_129_ = lean_string_append(v___x_127_, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
v___jp_81_:
{
lean_object* v_worklist_83_; lean_object* v_checked_84_; uint8_t v___x_85_; 
v_worklist_83_ = lean_ctor_get(v___y_82_, 0);
v_checked_84_ = lean_ctor_get(v___y_82_, 1);
v___x_85_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_checked_84_, v_n_78_);
if (v___x_85_ == 0)
{
lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_96_; 
lean_inc_ref(v_checked_84_);
lean_inc_ref(v_worklist_83_);
v_isSharedCheck_96_ = !lean_is_exclusive(v___y_82_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; lean_object* v_unused_98_; 
v_unused_97_ = lean_ctor_get(v___y_82_, 1);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v___y_82_, 0);
lean_dec(v_unused_98_);
v___x_87_ = v___y_82_;
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
else
{
lean_dec(v___y_82_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_96_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_89_ = lean_box(0);
v___x_90_ = lean_array_push(v_worklist_83_, v_n_78_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_90_);
v___x_92_ = v___x_87_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_checked_84_);
v___x_92_ = v_reuseFailAlloc_95_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_89_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_n_78_);
v___x_99_ = lean_box(0);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___y_82_);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___boxed(lean_object* v_n_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst(v_n_131_, v_a_132_, v_a_133_);
lean_dec_ref(v_a_132_);
return v_res_134_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0(lean_object* v_00_u03b2_135_, lean_object* v_m_136_, lean_object* v_a_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_m_136_, v_a_137_);
return v___x_138_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_136_ = stack[1].m_obj;
lean_object* v_a_137_ = stack[2].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0(lean_box(0), v_m_136_, v_a_137_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___boxed(lean_object* v_00_u03b2_140_, lean_object* v_m_141_, lean_object* v_a_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0(v_00_u03b2_140_, v_m_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_m_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1(lean_object* v_00_u03b2_145_, lean_object* v_m_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_m_146_, v_a_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___boxed(lean_object* v_00_u03b2_149_, lean_object* v_m_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1(v_00_u03b2_149_, v_m_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_m_150_);
return v_res_152_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0(lean_object* v_00_u03b2_153_, lean_object* v_a_154_, lean_object* v_x_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_154_, v_x_155_);
return v___x_156_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_154_ = stack[1].m_obj;
lean_object* v_x_155_ = stack[2].m_obj;
uint8_t v_res_157_;
v_res_157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0(lean_box(0), v_a_154_, v_x_155_);
stack->m_num = v_res_157_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___boxed(lean_object* v_00_u03b2_158_, lean_object* v_a_159_, lean_object* v_x_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0(v_00_u03b2_158_, v_a_159_, v_x_160_);
lean_dec(v_x_160_);
lean_dec(v_a_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2(lean_object* v_00_u03b2_163_, lean_object* v_a_164_, lean_object* v_x_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___redArg(v_a_164_, v_x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2___boxed(lean_object* v_00_u03b2_167_, lean_object* v_a_168_, lean_object* v_x_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1_spec__2(v_00_u03b2_167_, v_a_168_, v_x_169_);
lean_dec(v_x_169_);
lean_dec(v_a_168_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
return v_x_171_;
}
else
{
lean_object* v_key_173_; lean_object* v_value_174_; lean_object* v_tail_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_201_; 
v_key_173_ = lean_ctor_get(v_x_172_, 0);
v_value_174_ = lean_ctor_get(v_x_172_, 1);
v_tail_175_ = lean_ctor_get(v_x_172_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_172_);
if (v_isSharedCheck_201_ == 0)
{
v___x_177_ = v_x_172_;
v_isShared_178_ = v_isSharedCheck_201_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_tail_175_);
lean_inc(v_value_174_);
lean_inc(v_key_173_);
lean_dec(v_x_172_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_201_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; uint64_t v___y_181_; 
v___x_179_ = lean_array_get_size(v_x_171_);
if (lean_obj_tag(v_key_173_) == 0)
{
uint64_t v___x_199_; 
v___x_199_ = 1723ULL;
v___y_181_ = v___x_199_;
goto v___jp_180_;
}
else
{
uint64_t v_hash_200_; 
v_hash_200_ = lean_ctor_get_uint64(v_key_173_, sizeof(void*)*2);
v___y_181_ = v_hash_200_;
goto v___jp_180_;
}
v___jp_180_:
{
uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v_fold_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v___x_187_; size_t v___x_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_182_ = 32ULL;
v___x_183_ = lean_uint64_shift_right(v___y_181_, v___x_182_);
v_fold_184_ = lean_uint64_xor(v___y_181_, v___x_183_);
v___x_185_ = 16ULL;
v___x_186_ = lean_uint64_shift_right(v_fold_184_, v___x_185_);
v___x_187_ = lean_uint64_xor(v_fold_184_, v___x_186_);
v___x_188_ = lean_uint64_to_usize(v___x_187_);
v___x_189_ = lean_usize_of_nat(v___x_179_);
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_sub(v___x_189_, v___x_190_);
v___x_192_ = lean_usize_land(v___x_188_, v___x_191_);
v___x_193_ = lean_array_uget_borrowed(v_x_171_, v___x_192_);
lean_inc(v___x_193_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 2, v___x_193_);
v___x_195_ = v___x_177_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_key_173_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_value_174_);
lean_ctor_set(v_reuseFailAlloc_198_, 2, v___x_193_);
v___x_195_ = v_reuseFailAlloc_198_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = lean_array_uset(v_x_171_, v___x_192_, v___x_195_);
v_x_171_ = v___x_196_;
v_x_172_ = v_tail_175_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(lean_object* v_i_202_, lean_object* v_source_203_, lean_object* v_target_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_array_get_size(v_source_203_);
v___x_206_ = lean_nat_dec_lt(v_i_202_, v___x_205_);
if (v___x_206_ == 0)
{
lean_dec_ref(v_source_203_);
lean_dec(v_i_202_);
return v_target_204_;
}
else
{
lean_object* v_es_207_; lean_object* v___x_208_; lean_object* v_source_209_; lean_object* v_target_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_es_207_ = lean_array_fget(v_source_203_, v_i_202_);
v___x_208_ = lean_box(0);
v_source_209_ = lean_array_fset(v_source_203_, v_i_202_, v___x_208_);
v_target_210_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(v_target_204_, v_es_207_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_i_202_, v___x_211_);
lean_dec(v_i_202_);
v_i_202_ = v___x_212_;
v_source_203_ = v_source_209_;
v_target_204_ = v_target_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(lean_object* v_data_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_nbuckets_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_215_ = lean_array_get_size(v_data_214_);
v___x_216_ = lean_unsigned_to_nat(2u);
v_nbuckets_217_ = lean_nat_mul(v___x_215_, v___x_216_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_box(0);
v___x_220_ = lean_mk_array(v_nbuckets_217_, v___x_219_);
v___x_221_ = lean_array_propagate_mark(v_data_214_, v___x_220_);
v___x_222_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(v___x_218_, v_data_214_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(lean_object* v_m_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
lean_object* v_size_226_; lean_object* v_buckets_227_; lean_object* v___x_228_; uint64_t v___y_230_; 
v_size_226_ = lean_ctor_get(v_m_223_, 0);
v_buckets_227_ = lean_ctor_get(v_m_223_, 1);
v___x_228_ = lean_array_get_size(v_buckets_227_);
if (lean_obj_tag(v_a_224_) == 0)
{
uint64_t v___x_267_; 
v___x_267_ = 1723ULL;
v___y_230_ = v___x_267_;
goto v___jp_229_;
}
else
{
uint64_t v_hash_268_; 
v_hash_268_ = lean_ctor_get_uint64(v_a_224_, sizeof(void*)*2);
v___y_230_ = v_hash_268_;
goto v___jp_229_;
}
v___jp_229_:
{
uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v_fold_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v_bkt_242_; uint8_t v___x_243_; 
v___x_231_ = 32ULL;
v___x_232_ = lean_uint64_shift_right(v___y_230_, v___x_231_);
v_fold_233_ = lean_uint64_xor(v___y_230_, v___x_232_);
v___x_234_ = 16ULL;
v___x_235_ = lean_uint64_shift_right(v_fold_233_, v___x_234_);
v___x_236_ = lean_uint64_xor(v_fold_233_, v___x_235_);
v___x_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = lean_usize_of_nat(v___x_228_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_sub(v___x_238_, v___x_239_);
v___x_241_ = lean_usize_land(v___x_237_, v___x_240_);
v_bkt_242_ = lean_array_uget_borrowed(v_buckets_227_, v___x_241_);
v___x_243_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_224_, v_bkt_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_264_; 
lean_inc_ref(v_buckets_227_);
lean_inc(v_size_226_);
v_isSharedCheck_264_ = !lean_is_exclusive(v_m_223_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_265_ = lean_ctor_get(v_m_223_, 1);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_m_223_, 0);
lean_dec(v_unused_266_);
v___x_245_ = v_m_223_;
v_isShared_246_ = v_isSharedCheck_264_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_m_223_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_264_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v_size_x27_248_; lean_object* v___x_249_; lean_object* v_buckets_x27_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_247_ = lean_unsigned_to_nat(1u);
v_size_x27_248_ = lean_nat_add(v_size_226_, v___x_247_);
lean_dec(v_size_226_);
lean_inc(v_bkt_242_);
v___x_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_249_, 0, v_a_224_);
lean_ctor_set(v___x_249_, 1, v_b_225_);
lean_ctor_set(v___x_249_, 2, v_bkt_242_);
v_buckets_x27_250_ = lean_array_uset(v_buckets_227_, v___x_241_, v___x_249_);
v___x_251_ = lean_unsigned_to_nat(4u);
v___x_252_ = lean_nat_mul(v_size_x27_248_, v___x_251_);
v___x_253_ = lean_unsigned_to_nat(3u);
v___x_254_ = lean_nat_div(v___x_252_, v___x_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_array_get_size(v_buckets_x27_250_);
v___x_256_ = lean_nat_dec_le(v___x_254_, v___x_255_);
lean_dec(v___x_254_);
if (v___x_256_ == 0)
{
lean_object* v_val_257_; lean_object* v___x_259_; 
v_val_257_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_buckets_x27_250_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_val_257_);
lean_ctor_set(v___x_245_, 0, v_size_x27_248_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_size_x27_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_val_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v___x_262_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_buckets_x27_250_);
lean_ctor_set(v___x_245_, 0, v_size_x27_248_);
v___x_262_ = v___x_245_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_size_x27_248_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_buckets_x27_250_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_dec(v_b_225_);
lean_dec(v_a_224_);
return v_m_223_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(lean_object* v_f_269_, lean_object* v_as_270_, size_t v_i_271_, size_t v_stop_272_, lean_object* v_b_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
uint8_t v___x_276_; 
v___x_276_ = lean_usize_dec_eq(v_i_271_, v_stop_272_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_array_uget_borrowed(v_as_270_, v_i_271_);
lean_inc_ref(v_f_269_);
lean_inc_ref(v___y_274_);
lean_inc(v___x_277_);
v___x_278_ = lean_apply_3(v_f_269_, v___x_277_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_dec_ref(v_f_269_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; lean_object* v_fst_280_; lean_object* v_snd_281_; size_t v___x_282_; size_t v___x_283_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v_fst_280_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_fst_280_);
v_snd_281_ = lean_ctor_get(v_a_279_, 1);
lean_inc(v_snd_281_);
lean_dec(v_a_279_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_271_, v___x_282_);
v_i_271_ = v___x_283_;
v_b_273_ = v_fst_280_;
v___y_275_ = v_snd_281_;
goto _start;
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v_f_269_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_b_273_);
lean_ctor_set(v___x_285_, 1, v___y_275_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_269_ = stack[0].m_obj;
lean_object* v_as_270_ = stack[1].m_obj;
size_t v_i_271_ = stack[2].m_num;
size_t v_stop_272_ = stack[3].m_num;
lean_object* v_b_273_ = stack[4].m_obj;
lean_object* v___y_274_ = stack[5].m_obj;
lean_object* v___y_275_ = stack[6].m_obj;
lean_object* v_res_287_;
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_269_, v_as_270_, v_i_271_, v_stop_272_, v_b_273_, v___y_274_, v___y_275_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed(lean_object* v_f_288_, lean_object* v_as_289_, lean_object* v_i_290_, lean_object* v_stop_291_, lean_object* v_b_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
size_t v_i_boxed_295_; size_t v_stop_boxed_296_; lean_object* v_res_297_; 
v_i_boxed_295_ = lean_unbox_usize(v_i_290_);
lean_dec(v_i_290_);
v_stop_boxed_296_ = lean_unbox_usize(v_stop_291_);
lean_dec(v_stop_291_);
v_res_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_288_, v_as_289_, v_i_boxed_295_, v_stop_boxed_296_, v_b_292_, v___y_293_, v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec_ref(v_as_289_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(lean_object* v_f_298_, lean_object* v_as_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
if (lean_obj_tag(v_as_299_) == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref(v_f_298_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___y_301_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
else
{
lean_object* v_head_305_; lean_object* v_tail_306_; lean_object* v_ctor_307_; lean_object* v_rhs_308_; lean_object* v___x_309_; 
v_head_305_ = lean_ctor_get(v_as_299_, 0);
lean_inc(v_head_305_);
v_tail_306_ = lean_ctor_get(v_as_299_, 1);
lean_inc(v_tail_306_);
lean_dec_ref_known(v_as_299_, 2);
v_ctor_307_ = lean_ctor_get(v_head_305_, 0);
lean_inc(v_ctor_307_);
v_rhs_308_ = lean_ctor_get(v_head_305_, 2);
lean_inc_ref(v_rhs_308_);
lean_dec(v_head_305_);
lean_inc_ref(v_f_298_);
lean_inc_ref(v___y_300_);
v___x_309_ = lean_apply_3(v_f_298_, v_ctor_307_, v___y_300_, v___y_301_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_dec_ref(v_rhs_308_);
lean_dec(v_tail_306_);
lean_dec_ref(v_f_298_);
return v___x_309_;
}
else
{
lean_object* v_a_310_; lean_object* v_snd_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_snd_311_ = lean_ctor_get(v_a_310_, 1);
lean_inc(v_snd_311_);
lean_dec(v_a_310_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l_Lean_Expr_getUsedConstants(v_rhs_308_);
v___x_314_ = lean_array_get_size(v___x_313_);
v___x_315_ = lean_nat_dec_lt(v___x_312_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v___x_313_);
v_as_299_ = v_tail_306_;
v___y_301_ = v_snd_311_;
goto _start;
}
else
{
lean_object* v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_box(0);
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_314_);
lean_inc_ref(v_f_298_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_298_, v___x_313_, v___x_318_, v___x_319_, v___x_317_, v___y_300_, v_snd_311_);
lean_dec_ref(v___x_313_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_dec(v_tail_306_);
lean_dec_ref(v_f_298_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v_snd_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v_snd_322_ = lean_ctor_get(v_a_321_, 1);
lean_inc(v_snd_322_);
lean_dec(v_a_321_);
v_as_299_ = v_tail_306_;
v___y_301_ = v_snd_322_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2___boxed(lean_object* v_f_324_, lean_object* v_as_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(v_f_324_, v_as_325_, v___y_326_, v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(lean_object* v_f_329_, lean_object* v_as_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
if (lean_obj_tag(v_as_330_) == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_f_329_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___y_332_);
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
else
{
lean_object* v_head_336_; lean_object* v_tail_337_; lean_object* v___x_338_; 
v_head_336_ = lean_ctor_get(v_as_330_, 0);
lean_inc(v_head_336_);
v_tail_337_ = lean_ctor_get(v_as_330_, 1);
lean_inc(v_tail_337_);
lean_dec_ref_known(v_as_330_, 2);
lean_inc_ref(v_f_329_);
lean_inc_ref(v___y_331_);
v___x_338_ = lean_apply_3(v_f_329_, v_head_336_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_dec(v_tail_337_);
lean_dec_ref(v_f_329_);
return v___x_338_;
}
else
{
lean_object* v_a_339_; lean_object* v_snd_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v_snd_340_ = lean_ctor_get(v_a_339_, 1);
lean_inc(v_snd_340_);
lean_dec(v_a_339_);
v_as_330_ = v_tail_337_;
v___y_332_ = v_snd_340_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1___boxed(lean_object* v_f_342_, lean_object* v_as_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_342_, v_as_343_, v___y_344_, v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(lean_object* v___x_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_347_);
lean_ctor_set(v___x_350_, 1, v___y_349_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0___boxed(lean_object* v___x_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___lam__0(v___x_352_, v___y_353_, v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(lean_object* v_info_360_, lean_object* v_f_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___y_387_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_383_ = l_Lean_ConstantInfo_type(v_info_360_);
v___x_384_ = l_Lean_Expr_getUsedConstants(v___x_383_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_array_get_size(v___x_384_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_nat_dec_lt(v___x_385_, v___x_407_);
if (v___x_409_ == 0)
{
lean_object* v___f_410_; 
lean_dec_ref(v___x_384_);
v___f_410_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___closed__0));
v___y_387_ = v___f_410_;
goto v___jp_386_;
}
else
{
size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_usize_of_nat(v___x_407_);
v___x_412_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1));
v___x_413_ = lean_box_usize(v___x_411_);
lean_inc_ref(v_f_361_);
v___x_414_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0___boxed), 7, 5);
lean_closure_set(v___x_414_, 0, v_f_361_);
lean_closure_set(v___x_414_, 1, v___x_384_);
lean_closure_set(v___x_414_, 2, v___x_412_);
lean_closure_set(v___x_414_, 3, v___x_413_);
lean_closure_set(v___x_414_, 4, v___x_408_);
v___y_387_ = v___x_414_;
goto v___jp_386_;
}
v___jp_364_:
{
switch(lean_obj_tag(v_info_360_))
{
case 5:
{
lean_object* v_val_367_; lean_object* v_all_368_; lean_object* v_ctors_369_; lean_object* v___x_370_; 
v_val_367_ = lean_ctor_get(v_info_360_, 0);
lean_inc_ref(v_val_367_);
lean_dec_ref_known(v_info_360_, 1);
v_all_368_ = lean_ctor_get(v_val_367_, 3);
lean_inc(v_all_368_);
v_ctors_369_ = lean_ctor_get(v_val_367_, 4);
lean_inc(v_ctors_369_);
lean_dec_ref(v_val_367_);
lean_inc_ref(v_f_361_);
v___x_370_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_361_, v_ctors_369_, v___y_365_, v___y_366_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_dec(v_all_368_);
lean_dec_ref(v_f_361_);
return v___x_370_;
}
else
{
lean_object* v_a_371_; lean_object* v_snd_372_; lean_object* v___x_373_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v_snd_372_ = lean_ctor_get(v_a_371_, 1);
lean_inc(v_snd_372_);
lean_dec(v_a_371_);
v___x_373_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__1(v_f_361_, v_all_368_, v___y_365_, v_snd_372_);
return v___x_373_;
}
}
case 6:
{
lean_object* v_val_374_; lean_object* v_induct_375_; lean_object* v___x_376_; 
v_val_374_ = lean_ctor_get(v_info_360_, 0);
lean_inc_ref(v_val_374_);
lean_dec_ref_known(v_info_360_, 1);
v_induct_375_ = lean_ctor_get(v_val_374_, 1);
lean_inc(v_induct_375_);
lean_dec_ref(v_val_374_);
lean_inc_ref(v___y_365_);
v___x_376_ = lean_apply_3(v_f_361_, v_induct_375_, v___y_365_, v___y_366_);
return v___x_376_;
}
case 7:
{
lean_object* v_val_377_; lean_object* v_rules_378_; lean_object* v___x_379_; 
v_val_377_ = lean_ctor_get(v_info_360_, 0);
lean_inc_ref(v_val_377_);
lean_dec_ref_known(v_info_360_, 1);
v_rules_378_ = lean_ctor_get(v_val_377_, 6);
lean_inc(v_rules_378_);
lean_dec_ref(v_val_377_);
v___x_379_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__2(v_f_361_, v_rules_378_, v___y_365_, v___y_366_);
return v___x_379_;
}
default: 
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec_ref(v_f_361_);
lean_dec_ref(v_info_360_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___y_366_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
v___jp_386_:
{
lean_object* v___x_388_; 
lean_inc_ref(v___y_362_);
v___x_388_ = lean_apply_2(v___y_387_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_dec_ref(v_f_361_);
lean_dec_ref(v_info_360_);
return v___x_388_;
}
else
{
lean_object* v_a_389_; lean_object* v_snd_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v_snd_390_ = lean_ctor_get(v_a_389_, 1);
lean_inc(v_snd_390_);
lean_dec(v_a_389_);
v___x_391_ = l_Lean_ConstantInfo_name(v_info_360_);
lean_inc_ref(v_f_361_);
lean_inc_ref(v___y_362_);
v___x_392_ = lean_apply_3(v_f_361_, v___x_391_, v___y_362_, v_snd_390_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref(v_f_361_);
lean_dec_ref(v_info_360_);
return v___x_392_;
}
else
{
lean_object* v_a_393_; lean_object* v_snd_394_; uint8_t v___x_395_; lean_object* v___x_396_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v_snd_394_ = lean_ctor_get(v_a_393_, 1);
lean_inc(v_snd_394_);
lean_dec(v_a_393_);
v___x_395_ = 1;
lean_inc_ref(v_info_360_);
v___x_396_ = l_Lean_ConstantInfo_value_x3f(v_info_360_, v___x_395_);
if (lean_obj_tag(v___x_396_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_val_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_396_, 1);
v___x_398_ = l_Lean_Expr_getUsedConstants(v_val_397_);
v___x_399_ = lean_array_get_size(v___x_398_);
v___x_400_ = lean_nat_dec_lt(v___x_385_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec_ref(v___x_398_);
v___y_365_ = v___y_362_;
v___y_366_ = v_snd_394_;
goto v___jp_364_;
}
else
{
lean_object* v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
v___x_402_ = ((size_t)0ULL);
v___x_403_ = lean_usize_of_nat(v___x_399_);
lean_inc_ref(v_f_361_);
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0_spec__0(v_f_361_, v___x_398_, v___x_402_, v___x_403_, v___x_401_, v___y_362_, v_snd_394_);
lean_dec_ref(v___x_398_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_dec_ref(v_f_361_);
lean_dec_ref(v_info_360_);
return v___x_404_;
}
else
{
lean_object* v_a_405_; lean_object* v_snd_406_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v_snd_406_ = lean_ctor_get(v_a_405_, 1);
lean_inc(v_snd_406_);
lean_dec(v_a_405_);
v___y_365_ = v___y_362_;
v___y_366_ = v_snd_406_;
goto v___jp_364_;
}
}
}
else
{
lean_dec(v___x_396_);
v___y_365_ = v___y_362_;
v___y_366_ = v_snd_394_;
goto v___jp_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed(lean_object* v_info_415_, lean_object* v_f_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(v_info_415_, v_f_416_, v___y_417_, v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_worklist_423_; lean_object* v_checked_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_worklist_423_ = lean_ctor_get(v_a_422_, 0);
v_checked_424_ = lean_ctor_get(v_a_422_, 1);
v___x_425_ = lean_array_get_size(v_worklist_423_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_nat_dec_eq(v___x_425_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_468_; 
lean_inc_ref(v_checked_424_);
lean_inc_ref(v_worklist_423_);
v_isSharedCheck_468_ = !lean_is_exclusive(v_a_422_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; lean_object* v_unused_470_; 
v_unused_469_ = lean_ctor_get(v_a_422_, 1);
lean_dec(v_unused_469_);
v_unused_470_ = lean_ctor_get(v_a_422_, 0);
lean_dec(v_unused_470_);
v___x_429_ = v_a_422_;
v_isShared_430_ = v_isSharedCheck_468_;
goto v_resetjp_428_;
}
else
{
lean_dec(v_a_422_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_468_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_431_ = lean_box(0);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_sub(v___x_425_, v___x_432_);
v___x_434_ = lean_array_get(v___x_431_, v_worklist_423_, v___x_433_);
lean_dec(v___x_433_);
v___x_435_ = lean_array_pop(v_worklist_423_);
lean_inc_ref(v_checked_424_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_435_);
v___x_437_ = v___x_429_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_checked_424_);
v___x_437_ = v_reuseFailAlloc_467_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
uint8_t v___x_438_; 
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_checked_424_, v___x_434_);
lean_dec_ref(v_checked_424_);
if (v___x_438_ == 0)
{
lean_object* v_solution_439_; lean_object* v_constMap_440_; lean_object* v___x_441_; 
v_solution_439_ = lean_ctor_get(v_a_421_, 0);
v_constMap_440_ = lean_ctor_get(v_solution_439_, 0);
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_440_, v___x_434_);
if (lean_obj_tag(v___x_441_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_val_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_val_442_);
lean_dec_ref_known(v___x_441_, 1);
v___x_443_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___closed__0));
v___x_444_ = l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0(v_val_442_, v___x_443_, v_a_421_, v___x_437_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec(v___x_434_);
return v___x_444_;
}
else
{
lean_object* v_a_445_; lean_object* v_snd_446_; lean_object* v_worklist_447_; lean_object* v_checked_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_458_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v_snd_446_ = lean_ctor_get(v_a_445_, 1);
lean_inc(v_snd_446_);
lean_dec(v_a_445_);
v_worklist_447_ = lean_ctor_get(v_snd_446_, 0);
v_checked_448_ = lean_ctor_get(v_snd_446_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v_snd_446_);
if (v_isSharedCheck_458_ == 0)
{
v___x_450_ = v_snd_446_;
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_checked_448_);
lean_inc(v_worklist_447_);
lean_dec(v_snd_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_458_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_box(0);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_checked_448_, v___x_434_, v___x_452_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_worklist_447_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v_a_422_ = v___x_455_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_441_);
lean_dec_ref(v___x_437_);
v___x_459_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__2));
v___x_460_ = 1;
v___x_461_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_434_, v___x_460_);
v___x_462_ = lean_string_append(v___x_459_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_464_ = lean_string_append(v___x_462_, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
else
{
lean_dec(v___x_434_);
v_a_422_ = v___x_437_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_a_422_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop___boxed(lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v_a_474_, v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1(lean_object* v_00_u03b2_477_, lean_object* v_m_478_, lean_object* v_a_479_, lean_object* v_b_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_m_478_, v_a_479_, v_b_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4(lean_object* v_00_u03b2_482_, lean_object* v_data_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_data_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_485_, lean_object* v_i_486_, lean_object* v_source_487_, lean_object* v_target_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5___redArg(v_i_486_, v_source_487_, v_target_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4_spec__5_spec__6___redArg(v_x_491_, v_x_492_);
return v___x_493_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(lean_object* v_f_494_, lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_fst_503_; lean_object* v_snd_504_; size_t v___x_505_; size_t v___x_506_; 
v___x_501_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
lean_inc_ref(v_f_494_);
lean_inc(v___x_501_);
v___x_502_ = lean_apply_2(v_f_494_, v___x_501_, v___y_499_);
v_fst_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_fst_503_);
v_snd_504_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_snd_504_);
lean_dec_ref(v___x_502_);
v___x_505_ = ((size_t)1ULL);
v___x_506_ = lean_usize_add(v_i_496_, v___x_505_);
v_i_496_ = v___x_506_;
v_b_498_ = v_fst_503_;
v___y_499_ = v_snd_504_;
goto _start;
}
else
{
lean_object* v___x_508_; 
lean_dec_ref(v_f_494_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_b_498_);
lean_ctor_set(v___x_508_, 1, v___y_499_);
return v___x_508_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_494_ = stack[0].m_obj;
lean_object* v_as_495_ = stack[1].m_obj;
size_t v_i_496_ = stack[2].m_num;
size_t v_stop_497_ = stack[3].m_num;
lean_object* v_b_498_ = stack[4].m_obj;
lean_object* v___y_499_ = stack[5].m_obj;
lean_object* v_res_509_;
v_res_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_494_, v_as_495_, v_i_496_, v_stop_497_, v_b_498_, v___y_499_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed(lean_object* v_f_510_, lean_object* v_as_511_, lean_object* v_i_512_, lean_object* v_stop_513_, lean_object* v_b_514_, lean_object* v___y_515_){
_start:
{
size_t v_i_boxed_516_; size_t v_stop_boxed_517_; lean_object* v_res_518_; 
v_i_boxed_516_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_stop_boxed_517_ = lean_unbox_usize(v_stop_513_);
lean_dec(v_stop_513_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_510_, v_as_511_, v_i_boxed_516_, v_stop_boxed_517_, v_b_514_, v___y_515_);
lean_dec_ref(v_as_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(lean_object* v_f_519_, lean_object* v_as_520_, lean_object* v___y_521_){
_start:
{
if (lean_obj_tag(v_as_520_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_f_519_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___y_521_);
return v___x_523_;
}
else
{
lean_object* v_head_524_; lean_object* v_tail_525_; lean_object* v_ctor_526_; lean_object* v_rhs_527_; lean_object* v___x_528_; lean_object* v_snd_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_head_524_ = lean_ctor_get(v_as_520_, 0);
lean_inc(v_head_524_);
v_tail_525_ = lean_ctor_get(v_as_520_, 1);
lean_inc(v_tail_525_);
lean_dec_ref_known(v_as_520_, 2);
v_ctor_526_ = lean_ctor_get(v_head_524_, 0);
lean_inc(v_ctor_526_);
v_rhs_527_ = lean_ctor_get(v_head_524_, 2);
lean_inc_ref(v_rhs_527_);
lean_dec(v_head_524_);
lean_inc_ref(v_f_519_);
v___x_528_ = lean_apply_2(v_f_519_, v_ctor_526_, v___y_521_);
v_snd_529_ = lean_ctor_get(v___x_528_, 1);
lean_inc(v_snd_529_);
lean_dec_ref(v___x_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = l_Lean_Expr_getUsedConstants(v_rhs_527_);
v___x_532_ = lean_array_get_size(v___x_531_);
v___x_533_ = lean_nat_dec_lt(v___x_530_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec_ref(v___x_531_);
v_as_520_ = v_tail_525_;
v___y_521_ = v_snd_529_;
goto _start;
}
else
{
lean_object* v___x_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; lean_object* v_snd_539_; 
v___x_535_ = lean_box(0);
v___x_536_ = ((size_t)0ULL);
v___x_537_ = lean_usize_of_nat(v___x_532_);
lean_inc_ref(v_f_519_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_519_, v___x_531_, v___x_536_, v___x_537_, v___x_535_, v_snd_529_);
lean_dec_ref(v___x_531_);
v_snd_539_ = lean_ctor_get(v___x_538_, 1);
lean_inc(v_snd_539_);
lean_dec_ref(v___x_538_);
v_as_520_ = v_tail_525_;
v___y_521_ = v_snd_539_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(lean_object* v_f_541_, lean_object* v_as_542_, lean_object* v___y_543_){
_start:
{
if (lean_obj_tag(v_as_542_) == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v_f_541_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___y_543_);
return v___x_545_;
}
else
{
lean_object* v_head_546_; lean_object* v_tail_547_; lean_object* v___x_548_; lean_object* v_snd_549_; 
v_head_546_ = lean_ctor_get(v_as_542_, 0);
lean_inc(v_head_546_);
v_tail_547_ = lean_ctor_get(v_as_542_, 1);
lean_inc(v_tail_547_);
lean_dec_ref_known(v_as_542_, 2);
lean_inc_ref(v_f_541_);
v___x_548_ = lean_apply_2(v_f_541_, v_head_546_, v___y_543_);
v_snd_549_ = lean_ctor_get(v___x_548_, 1);
lean_inc(v_snd_549_);
lean_dec_ref(v___x_548_);
v_as_542_ = v_tail_547_;
v___y_543_ = v_snd_549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___lam__0(lean_object* v___x_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___y_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(lean_object* v_info_556_, lean_object* v_f_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___y_560_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___y_579_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_575_ = l_Lean_ConstantInfo_type(v_info_556_);
v___x_576_ = l_Lean_Expr_getUsedConstants(v___x_575_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_array_get_size(v___x_576_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_nat_dec_lt(v___x_577_, v___x_596_);
if (v___x_598_ == 0)
{
lean_object* v___f_599_; 
lean_dec_ref(v___x_576_);
v___f_599_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0___closed__0));
v___y_579_ = v___f_599_;
goto v___jp_578_;
}
else
{
size_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = lean_usize_of_nat(v___x_596_);
v___x_601_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__0___boxed__const__1));
v___x_602_ = lean_box_usize(v___x_600_);
lean_inc_ref(v_f_557_);
v___x_603_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed), 6, 5);
lean_closure_set(v___x_603_, 0, v_f_557_);
lean_closure_set(v___x_603_, 1, v___x_576_);
lean_closure_set(v___x_603_, 2, v___x_601_);
lean_closure_set(v___x_603_, 3, v___x_602_);
lean_closure_set(v___x_603_, 4, v___x_597_);
v___y_579_ = v___x_603_;
goto v___jp_578_;
}
v___jp_559_:
{
switch(lean_obj_tag(v_info_556_))
{
case 5:
{
lean_object* v_val_561_; lean_object* v_all_562_; lean_object* v_ctors_563_; lean_object* v___x_564_; lean_object* v_snd_565_; lean_object* v___x_566_; 
v_val_561_ = lean_ctor_get(v_info_556_, 0);
lean_inc_ref(v_val_561_);
lean_dec_ref_known(v_info_556_, 1);
v_all_562_ = lean_ctor_get(v_val_561_, 3);
lean_inc(v_all_562_);
v_ctors_563_ = lean_ctor_get(v_val_561_, 4);
lean_inc(v_ctors_563_);
lean_dec_ref(v_val_561_);
lean_inc_ref(v_f_557_);
v___x_564_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(v_f_557_, v_ctors_563_, v___y_560_);
v_snd_565_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_snd_565_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__1(v_f_557_, v_all_562_, v_snd_565_);
return v___x_566_;
}
case 6:
{
lean_object* v_val_567_; lean_object* v_induct_568_; lean_object* v___x_569_; 
v_val_567_ = lean_ctor_get(v_info_556_, 0);
lean_inc_ref(v_val_567_);
lean_dec_ref_known(v_info_556_, 1);
v_induct_568_ = lean_ctor_get(v_val_567_, 1);
lean_inc(v_induct_568_);
lean_dec_ref(v_val_567_);
v___x_569_ = lean_apply_2(v_f_557_, v_induct_568_, v___y_560_);
return v___x_569_;
}
case 7:
{
lean_object* v_val_570_; lean_object* v_rules_571_; lean_object* v___x_572_; 
v_val_570_ = lean_ctor_get(v_info_556_, 0);
lean_inc_ref(v_val_570_);
lean_dec_ref_known(v_info_556_, 1);
v_rules_571_ = lean_ctor_get(v_val_570_, 6);
lean_inc(v_rules_571_);
lean_dec_ref(v_val_570_);
v___x_572_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__2(v_f_557_, v_rules_571_, v___y_560_);
return v___x_572_;
}
default: 
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_f_557_);
lean_dec_ref(v_info_556_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___y_560_);
return v___x_574_;
}
}
}
v___jp_578_:
{
lean_object* v___x_580_; lean_object* v_snd_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_snd_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v___x_580_ = lean_apply_1(v___y_579_, v___y_558_);
v_snd_581_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_snd_581_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_ConstantInfo_name(v_info_556_);
lean_inc_ref(v_f_557_);
v___x_583_ = lean_apply_2(v_f_557_, v___x_582_, v_snd_581_);
v_snd_584_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_584_);
lean_dec_ref(v___x_583_);
v___x_585_ = 1;
lean_inc_ref(v_info_556_);
v___x_586_ = l_Lean_ConstantInfo_value_x3f(v_info_556_, v___x_585_);
if (lean_obj_tag(v___x_586_) == 1)
{
lean_object* v_val_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_val_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = l_Lean_Expr_getUsedConstants(v_val_587_);
v___x_589_ = lean_array_get_size(v___x_588_);
v___x_590_ = lean_nat_dec_lt(v___x_577_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec_ref(v___x_588_);
v___y_560_ = v_snd_584_;
goto v___jp_559_;
}
else
{
lean_object* v___x_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; lean_object* v_snd_595_; 
v___x_591_ = lean_box(0);
v___x_592_ = ((size_t)0ULL);
v___x_593_ = lean_usize_of_nat(v___x_589_);
lean_inc_ref(v_f_557_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_f_557_, v___x_588_, v___x_592_, v___x_593_, v___x_591_, v_snd_584_);
lean_dec_ref(v___x_588_);
v_snd_595_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_snd_595_);
lean_dec_ref(v___x_594_);
v___y_560_ = v_snd_595_;
goto v___jp_559_;
}
}
else
{
lean_dec(v___x_586_);
v___y_560_ = v_snd_584_;
goto v___jp_559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(lean_object* v_a_604_, lean_object* v_constMap_605_, lean_object* v___x_606_, lean_object* v_ref_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = lean_name_eq(v_ref_607_, v_a_604_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_605_, v_ref_607_);
if (lean_obj_tag(v___x_610_) == 1)
{
lean_object* v_val_611_; 
v_val_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_610_, 1);
if (lean_obj_tag(v_val_611_) == 0)
{
lean_object* v_fst_612_; lean_object* v_snd_613_; uint8_t v___x_614_; 
lean_dec_ref_known(v_val_611_, 1);
v_fst_612_ = lean_ctor_get(v___y_608_, 0);
v_snd_613_ = lean_ctor_get(v___y_608_, 1);
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0___redArg(v_fst_612_, v_ref_607_);
if (v___x_614_ == 0)
{
lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
lean_inc(v_snd_613_);
lean_inc(v_fst_612_);
v_isSharedCheck_625_ = !lean_is_exclusive(v___y_608_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; lean_object* v_unused_627_; 
v_unused_626_ = lean_ctor_get(v___y_608_, 1);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v___y_608_, 0);
lean_dec(v_unused_627_);
v___x_616_ = v___y_608_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_dec(v___y_608_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
lean_inc(v_ref_607_);
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_fst_612_, v_ref_607_, v___x_606_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v_a_604_);
lean_ctor_set(v___x_616_, 0, v_ref_607_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_ref_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_a_604_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_array_push(v_snd_613_, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_618_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_606_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
return v___x_623_;
}
}
}
else
{
lean_object* v___x_628_; 
lean_dec(v_ref_607_);
lean_dec(v_a_604_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_606_);
lean_ctor_set(v___x_628_, 1, v___y_608_);
return v___x_628_;
}
}
else
{
lean_object* v___x_629_; 
lean_dec(v_val_611_);
lean_dec(v_ref_607_);
lean_dec(v_a_604_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_606_);
lean_ctor_set(v___x_629_, 1, v___y_608_);
return v___x_629_;
}
}
else
{
lean_object* v___x_630_; 
lean_dec(v___x_610_);
lean_dec(v_ref_607_);
lean_dec(v_a_604_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_606_);
lean_ctor_set(v___x_630_, 1, v___y_608_);
return v___x_630_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_ref_607_);
lean_dec(v_a_604_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_606_);
lean_ctor_set(v___x_631_, 1, v___y_608_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed(lean_object* v_a_632_, lean_object* v_constMap_633_, lean_object* v___x_634_, lean_object* v_ref_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0(v_a_632_, v_constMap_633_, v___x_634_, v_ref_635_, v___y_636_);
lean_dec_ref(v_constMap_633_);
return v_res_637_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(lean_object* v_env_638_, lean_object* v_as_639_, size_t v_sz_640_, size_t v_i_641_, lean_object* v_b_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_a_645_; lean_object* v_snd_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_lt(v_i_641_, v_sz_640_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec_ref(v_env_638_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v_b_642_);
lean_ctor_set(v___x_651_, 1, v___y_643_);
return v___x_651_;
}
else
{
lean_object* v_constMap_652_; lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_655_; 
v_constMap_652_ = lean_ctor_get(v_env_638_, 0);
v___x_653_ = lean_box(0);
v_a_654_ = lean_array_uget_borrowed(v_as_639_, v_i_641_);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_652_, v_a_654_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v_snd_659_; 
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref_known(v___x_655_, 1);
lean_inc_ref(v_constMap_652_);
lean_inc(v_a_654_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___lam__0___boxed), 5, 3);
lean_closure_set(v___f_657_, 0, v_a_654_);
lean_closure_set(v___f_657_, 1, v_constMap_652_);
lean_closure_set(v___f_657_, 2, v___x_653_);
v___x_658_ = l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__0(v_val_656_, v___f_657_, v___y_643_);
v_snd_659_ = lean_ctor_get(v___x_658_, 1);
lean_inc(v_snd_659_);
lean_dec_ref(v___x_658_);
v_a_645_ = v___x_653_;
v_snd_646_ = v_snd_659_;
goto v___jp_644_;
}
else
{
lean_dec(v___x_655_);
v_a_645_ = v___x_653_;
v_snd_646_ = v___y_643_;
goto v___jp_644_;
}
}
v___jp_644_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_641_, v___x_647_);
v_i_641_ = v___x_648_;
v_b_642_ = v_a_645_;
v___y_643_ = v_snd_646_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_638_ = stack[0].m_obj;
lean_object* v_as_639_ = stack[1].m_obj;
size_t v_sz_640_ = stack[2].m_num;
size_t v_i_641_ = stack[3].m_num;
lean_object* v_b_642_ = stack[4].m_obj;
lean_object* v___y_643_ = stack[5].m_obj;
lean_object* v_res_660_;
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_638_, v_as_639_, v_sz_640_, v_i_641_, v_b_642_, v___y_643_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1___boxed(lean_object* v_env_661_, lean_object* v_as_662_, lean_object* v_sz_663_, lean_object* v_i_664_, lean_object* v_b_665_, lean_object* v___y_666_){
_start:
{
size_t v_sz_boxed_667_; size_t v_i_boxed_668_; lean_object* v_res_669_; 
v_sz_boxed_667_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v_i_boxed_668_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_661_, v_as_662_, v_sz_boxed_667_, v_i_boxed_668_, v_b_665_, v___y_666_);
lean_dec_ref(v_as_662_);
return v_res_669_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__0(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_box(0);
v___x_671_ = lean_unsigned_to_nat(16u);
v___x_672_ = lean_mk_array(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__1(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__0, &l_Lake_Check_usedAxioms___closed__0_once, _init_l_Lake_Check_usedAxioms___closed__0);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_673_);
return v___x_675_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__3(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = ((lean_object*)(l_Lake_Check_usedAxioms___closed__2));
v___x_679_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_usedAxioms(lean_object* v_env_681_){
_start:
{
lean_object* v_constOrder_682_; lean_object* v___x_683_; size_t v_sz_684_; size_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_snd_688_; lean_object* v_snd_689_; 
v_constOrder_682_ = lean_ctor_get(v_env_681_, 1);
lean_inc_ref(v_constOrder_682_);
v___x_683_ = lean_box(0);
v_sz_684_ = lean_array_size(v_constOrder_682_);
v___x_685_ = ((size_t)0ULL);
v___x_686_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__3, &l_Lake_Check_usedAxioms___closed__3_once, _init_l_Lake_Check_usedAxioms___closed__3);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__1(v_env_681_, v_constOrder_682_, v_sz_684_, v___x_685_, v___x_683_, v___x_686_);
lean_dec_ref(v_constOrder_682_);
v_snd_688_ = lean_ctor_get(v___x_687_, 1);
lean_inc(v_snd_688_);
lean_dec_ref(v___x_687_);
v_snd_689_ = lean_ctor_get(v_snd_688_, 1);
lean_inc(v_snd_689_);
lean_dec(v_snd_688_);
return v_snd_689_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(lean_object* v_as_690_, size_t v_sz_691_, size_t v_i_692_, lean_object* v_b_693_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_lt(v_i_692_, v_sz_691_);
if (v___x_694_ == 0)
{
return v_b_693_;
}
else
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v_r_697_; size_t v___x_698_; size_t v___x_699_; 
v_a_695_ = lean_array_uget_borrowed(v_as_690_, v_i_692_);
v___x_696_ = lean_box(0);
lean_inc(v_a_695_);
v_r_697_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_b_693_, v_a_695_, v___x_696_);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_add(v_i_692_, v___x_698_);
v_i_692_ = v___x_699_;
v_b_693_ = v_r_697_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_690_ = stack[0].m_obj;
size_t v_sz_691_ = stack[1].m_num;
size_t v_i_692_ = stack[2].m_num;
lean_object* v_b_693_ = stack[3].m_obj;
lean_object* v_res_701_;
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_as_690_, v_sz_691_, v_i_692_, v_b_693_);
stack->m_obj
 = v_res_701_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2___boxed(lean_object* v_as_702_, lean_object* v_sz_703_, lean_object* v_i_704_, lean_object* v_b_705_){
_start:
{
size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v_sz_boxed_706_ = lean_unbox_usize(v_sz_703_);
lean_dec(v_sz_703_);
v_i_boxed_707_ = lean_unbox_usize(v_i_704_);
lean_dec(v_i_704_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_as_702_, v_sz_boxed_706_, v_i_boxed_707_, v_b_705_);
lean_dec_ref(v_as_702_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(lean_object* v_m_709_, lean_object* v_l_710_){
_start:
{
size_t v_sz_711_; size_t v___x_712_; lean_object* v___x_713_; 
v_sz_711_ = lean_array_size(v_l_710_);
v___x_712_ = ((size_t)0ULL);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_l_710_, v_sz_711_, v___x_712_, v_m_709_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2___boxed(lean_object* v_m_714_, lean_object* v_l_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v_m_714_, v_l_715_);
lean_dec_ref(v_l_715_);
return v_res_716_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(lean_object* v_solution_719_, lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_723_);
return v___x_725_;
}
else
{
lean_object* v_constMap_726_; lean_object* v_a_727_; lean_object* v___x_728_; 
v_constMap_726_ = lean_ctor_get(v_solution_719_, 0);
v_a_727_ = lean_array_uget_borrowed(v_as_720_, v_i_722_);
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_726_, v_a_727_);
if (lean_obj_tag(v___x_728_) == 1)
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_748_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_748_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_748_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_748_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
if (lean_obj_tag(v_val_729_) == 2)
{
lean_object* v_val_733_; lean_object* v_toConstantVal_734_; lean_object* v_name_735_; lean_object* v___x_736_; size_t v___x_737_; size_t v___x_738_; 
lean_del_object(v___x_731_);
v_val_733_ = lean_ctor_get(v_val_729_, 0);
lean_inc_ref(v_val_733_);
lean_dec_ref_known(v_val_729_, 1);
v_toConstantVal_734_ = lean_ctor_get(v_val_733_, 0);
lean_inc_ref(v_toConstantVal_734_);
lean_dec_ref(v_val_733_);
v_name_735_ = lean_ctor_get(v_toConstantVal_734_, 0);
lean_inc(v_name_735_);
lean_dec_ref(v_toConstantVal_734_);
v___x_736_ = lean_array_push(v_b_723_, v_name_735_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_722_, v___x_737_);
v_i_722_ = v___x_738_;
v_b_723_ = v___x_736_;
goto _start;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_val_729_);
lean_dec_ref(v_b_723_);
v___x_740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0));
lean_inc(v_a_727_);
v___x_741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_727_, v___x_724_);
v___x_742_ = lean_string_append(v___x_740_, v___x_741_);
lean_dec_ref(v___x_741_);
v___x_743_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_744_ = lean_string_append(v___x_742_, v___x_743_);
if (v_isShared_732_ == 0)
{
lean_ctor_set_tag(v___x_731_, 0);
lean_ctor_set(v___x_731_, 0, v___x_744_);
v___x_746_ = v___x_731_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_728_);
lean_dec_ref(v_b_723_);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_727_);
v___x_750_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_727_, v___x_724_);
v___x_751_ = lean_string_append(v___x_749_, v___x_750_);
lean_dec_ref(v___x_750_);
v___x_752_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_753_ = lean_string_append(v___x_751_, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_solution_719_ = stack[0].m_obj;
lean_object* v_as_720_ = stack[1].m_obj;
size_t v_sz_721_ = stack[2].m_num;
size_t v_i_722_ = stack[3].m_num;
lean_object* v_b_723_ = stack[4].m_obj;
lean_object* v_res_755_;
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_719_, v_as_720_, v_sz_721_, v_i_722_, v_b_723_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___boxed(lean_object* v_solution_756_, lean_object* v_as_757_, lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_b_760_){
_start:
{
size_t v_sz_boxed_761_; size_t v_i_boxed_762_; lean_object* v_res_763_; 
v_sz_boxed_761_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_762_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_756_, v_as_757_, v_sz_boxed_761_, v_i_boxed_762_, v_b_760_);
lean_dec_ref(v_as_757_);
lean_dec_ref(v_solution_756_);
return v_res_763_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(lean_object* v_solution_765_, lean_object* v_as_766_, size_t v_sz_767_, size_t v_i_768_, lean_object* v_b_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_lt(v_i_768_, v_sz_767_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v_b_769_);
return v___x_771_;
}
else
{
lean_object* v_constMap_772_; lean_object* v_a_773_; lean_object* v___x_774_; 
v_constMap_772_ = lean_ctor_get(v_solution_765_, 0);
v_a_773_ = lean_array_uget_borrowed(v_as_766_, v_i_768_);
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_772_, v_a_773_);
if (lean_obj_tag(v___x_774_) == 1)
{
lean_object* v_val_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_794_; 
v_val_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_794_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_794_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_val_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_794_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
if (lean_obj_tag(v_val_775_) == 1)
{
lean_object* v_val_779_; lean_object* v_toConstantVal_780_; lean_object* v_name_781_; lean_object* v___x_782_; size_t v___x_783_; size_t v___x_784_; 
lean_del_object(v___x_777_);
v_val_779_ = lean_ctor_get(v_val_775_, 0);
lean_inc_ref(v_val_779_);
lean_dec_ref_known(v_val_775_, 1);
v_toConstantVal_780_ = lean_ctor_get(v_val_779_, 0);
lean_inc_ref(v_toConstantVal_780_);
lean_dec_ref(v_val_779_);
v_name_781_ = lean_ctor_get(v_toConstantVal_780_, 0);
lean_inc(v_name_781_);
lean_dec_ref(v_toConstantVal_780_);
v___x_782_ = lean_array_push(v_b_769_, v_name_781_);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_768_, v___x_783_);
v_i_768_ = v___x_784_;
v_b_769_ = v___x_782_;
goto _start;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v_val_775_);
lean_dec_ref(v_b_769_);
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0));
lean_inc(v_a_773_);
v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_773_, v___x_770_);
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
lean_dec_ref(v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 0);
lean_ctor_set(v___x_777_, 0, v___x_790_);
v___x_792_ = v___x_777_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v___x_774_);
lean_dec_ref(v_b_769_);
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_773_);
v___x_796_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_773_, v___x_770_);
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
lean_dec_ref(v___x_796_);
v___x_798_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_799_ = lean_string_append(v___x_797_, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_solution_765_ = stack[0].m_obj;
lean_object* v_as_766_ = stack[1].m_obj;
size_t v_sz_767_ = stack[2].m_num;
size_t v_i_768_ = stack[3].m_num;
lean_object* v_b_769_ = stack[4].m_obj;
lean_object* v_res_801_;
v_res_801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_765_, v_as_766_, v_sz_767_, v_i_768_, v_b_769_);
stack->m_obj
 = v_res_801_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___boxed(lean_object* v_solution_802_, lean_object* v_as_803_, lean_object* v_sz_804_, lean_object* v_i_805_, lean_object* v_b_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_804_);
lean_dec(v_sz_804_);
v_i_boxed_808_ = lean_unbox_usize(v_i_805_);
lean_dec(v_i_805_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_802_, v_as_803_, v_sz_boxed_807_, v_i_boxed_808_, v_b_806_);
lean_dec_ref(v_as_803_);
lean_dec_ref(v_solution_802_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms(lean_object* v_solution_812_, lean_object* v_theoremTargets_813_, lean_object* v_definitionTargets_814_, lean_object* v_legalAxioms_815_){
_start:
{
lean_object* v_worklist_816_; size_t v_sz_817_; size_t v___x_818_; lean_object* v___x_819_; 
v_worklist_816_ = ((lean_object*)(l_Lake_Check_checkAxioms___closed__0));
v_sz_817_ = lean_array_size(v_theoremTargets_813_);
v___x_818_ = ((size_t)0ULL);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_812_, v_theoremTargets_813_, v_sz_817_, v___x_818_, v_worklist_816_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_solution_812_);
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
lean_object* v_a_828_; size_t v_sz_829_; lean_object* v___x_830_; 
v_a_828_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_819_, 1);
v_sz_829_ = lean_array_size(v_definitionTargets_814_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_812_, v_definitionTargets_814_, v_sz_829_, v___x_818_, v_a_828_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_solution_812_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_839_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_830_, 1);
v___x_840_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v___x_840_, v_legalAxioms_815_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_solution_812_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_a_839_);
lean_ctor_set(v___x_843_, 1, v___x_840_);
v___x_844_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v___x_842_, v___x_843_);
lean_dec_ref_known(v___x_842_, 2);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_861_; 
v_a_853_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_861_ == 0)
{
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_861_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_fst_857_; lean_object* v___x_859_; 
v_fst_857_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_fst_857_);
lean_dec(v_a_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_fst_857_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_fst_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms___boxed(lean_object* v_solution_862_, lean_object* v_theoremTargets_863_, lean_object* v_definitionTargets_864_, lean_object* v_legalAxioms_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lake_Check_checkAxioms(v_solution_862_, v_theoremTargets_863_, v_definitionTargets_864_, v_legalAxioms_865_);
lean_dec_ref(v_legalAxioms_865_);
lean_dec_ref(v_definitionTargets_864_);
lean_dec_ref(v_theoremTargets_863_);
return v_res_866_;
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
