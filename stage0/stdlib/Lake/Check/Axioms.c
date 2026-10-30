// Lean compiler output
// Module: Lake.Check.Axioms
// Imports: public import LeanExport.Parse import Lake.Check.Util import Init.Data.ToString.Macro import Init.Data.Array.QSort import Lean.Data.Name import Std.Data.HashSet
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___closed__0 = (const lean_object*)&l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Check_usedAxioms_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Check_usedAxioms_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_usedAxioms_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_usedAxioms_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Check_usedAxioms___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_usedAxioms___closed__0;
static lean_once_cell_t l_Lake_Check_usedAxioms___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Check_usedAxioms___closed__1;
LEAN_EXPORT lean_object* l_Lake_Check_usedAxioms(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4(lean_object* v_f_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_, lean_object* v_b_493_, lean_object* v___y_494_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4___boxed(lean_object* v_f_504_, lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_stop_507_, lean_object* v_b_508_, lean_object* v___y_509_){
_start:
{
size_t v_i_boxed_510_; size_t v_stop_boxed_511_; lean_object* v_res_512_; 
v_i_boxed_510_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_stop_boxed_511_ = lean_unbox_usize(v_stop_507_);
lean_dec(v_stop_507_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4(v_f_504_, v_as_505_, v_i_boxed_510_, v_stop_boxed_511_, v_b_508_, v___y_509_);
lean_dec_ref(v_as_505_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__5(lean_object* v_f_513_, lean_object* v_as_514_, lean_object* v___y_515_){
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
lean_object* v_head_518_; lean_object* v_tail_519_; lean_object* v___x_520_; lean_object* v_snd_521_; 
v_head_518_ = lean_ctor_get(v_as_514_, 0);
lean_inc(v_head_518_);
v_tail_519_ = lean_ctor_get(v_as_514_, 1);
lean_inc(v_tail_519_);
lean_dec_ref_known(v_as_514_, 2);
lean_inc_ref(v_f_513_);
v___x_520_ = lean_apply_2(v_f_513_, v_head_518_, v___y_515_);
v_snd_521_ = lean_ctor_get(v___x_520_, 1);
lean_inc(v_snd_521_);
lean_dec_ref(v___x_520_);
v_as_514_ = v_tail_519_;
v___y_515_ = v_snd_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__6(lean_object* v_f_523_, lean_object* v_as_524_, lean_object* v___y_525_){
_start:
{
if (lean_obj_tag(v_as_524_) == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v_f_523_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___y_525_);
return v___x_527_;
}
else
{
lean_object* v_head_528_; lean_object* v_tail_529_; lean_object* v_ctor_530_; lean_object* v_rhs_531_; lean_object* v___x_532_; lean_object* v_snd_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_head_528_ = lean_ctor_get(v_as_524_, 0);
lean_inc(v_head_528_);
v_tail_529_ = lean_ctor_get(v_as_524_, 1);
lean_inc(v_tail_529_);
lean_dec_ref_known(v_as_524_, 2);
v_ctor_530_ = lean_ctor_get(v_head_528_, 0);
lean_inc(v_ctor_530_);
v_rhs_531_ = lean_ctor_get(v_head_528_, 2);
lean_inc_ref(v_rhs_531_);
lean_dec(v_head_528_);
lean_inc_ref(v_f_523_);
v___x_532_ = lean_apply_2(v_f_523_, v_ctor_530_, v___y_525_);
v_snd_533_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_532_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l_Lean_Expr_getUsedConstants(v_rhs_531_);
v___x_536_ = lean_array_get_size(v___x_535_);
v___x_537_ = lean_nat_dec_lt(v___x_534_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v___x_535_);
v_as_524_ = v_tail_529_;
v___y_525_ = v_snd_533_;
goto _start;
}
else
{
lean_object* v___x_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; lean_object* v_snd_543_; 
v___x_539_ = lean_box(0);
v___x_540_ = ((size_t)0ULL);
v___x_541_ = lean_usize_of_nat(v___x_536_);
lean_inc_ref(v_f_523_);
v___x_542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4(v_f_523_, v___x_535_, v___x_540_, v___x_541_, v___x_539_, v_snd_533_);
lean_dec_ref(v___x_535_);
v_snd_543_ = lean_ctor_get(v___x_542_, 1);
lean_inc(v_snd_543_);
lean_dec_ref(v___x_542_);
v_as_524_ = v_tail_529_;
v___y_525_ = v_snd_543_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___lam__0(lean_object* v___x_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___y_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2(lean_object* v_info_550_, lean_object* v_f_551_, lean_object* v___y_552_){
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
v___f_593_ = ((lean_object*)(l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2___closed__0));
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
v___x_597_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4___boxed), 6, 5);
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
v___x_558_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__5(v_f_551_, v_ctors_557_, v___y_554_);
v_snd_559_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_snd_559_);
lean_dec_ref(v___x_558_);
v___x_560_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__5(v_f_551_, v_all_556_, v_snd_559_);
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
v___x_566_ = l_List_forM___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__6(v_f_551_, v_rules_565_, v___y_554_);
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
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2_spec__4(v_f_551_, v___x_582_, v___x_586_, v___x_587_, v___x_585_, v_snd_578_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2___lam__0(lean_object* v_a_598_, lean_object* v_x_599_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_a_598_);
return v___x_600_;
}
else
{
lean_object* v_val_601_; uint8_t v___x_602_; 
v_val_601_ = lean_ctor_get(v_x_599_, 0);
v___x_602_ = l_Lean_Name_lt(v_a_598_, v_val_601_);
if (v___x_602_ == 0)
{
lean_dec(v_a_598_);
return v_x_599_;
}
else
{
lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_599_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v_x_599_, 0);
lean_dec(v_unused_610_);
v___x_604_ = v_x_599_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_dec(v_x_599_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_a_598_);
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_598_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2(lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2___lam__0(v_a_611_, v___x_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_dec(v_a_612_);
return v_x_613_;
}
else
{
lean_object* v_val_616_; lean_object* v___x_617_; 
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_617_, 0, v_a_612_);
lean_ctor_set(v___x_617_, 1, v_val_616_);
lean_ctor_set(v___x_617_, 2, v_x_613_);
return v___x_617_;
}
}
else
{
lean_object* v_key_618_; lean_object* v_value_619_; lean_object* v_tail_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_635_; 
v_key_618_ = lean_ctor_get(v_x_613_, 0);
v_value_619_ = lean_ctor_get(v_x_613_, 1);
v_tail_620_ = lean_ctor_get(v_x_613_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_635_ == 0)
{
v___x_622_ = v_x_613_;
v_isShared_623_ = v_isSharedCheck_635_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_tail_620_);
lean_inc(v_value_619_);
lean_inc(v_key_618_);
lean_dec(v_x_613_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_635_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
uint8_t v___x_624_; 
v___x_624_ = lean_name_eq(v_key_618_, v_a_612_);
if (v___x_624_ == 0)
{
lean_object* v_tail_625_; lean_object* v___x_627_; 
v_tail_625_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2(v_a_611_, v_a_612_, v_tail_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 2, v_tail_625_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_key_618_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_value_619_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_tail_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v_key_618_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v_value_619_);
v___x_630_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2___lam__0(v_a_611_, v___x_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_del_object(v___x_622_);
lean_dec(v_a_612_);
return v_tail_620_;
}
else
{
lean_object* v_val_631_; lean_object* v___x_633_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v___x_630_, 1);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_val_631_);
lean_ctor_set(v___x_622_, 0, v_a_612_);
v___x_633_ = v___x_622_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_612_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_val_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_tail_620_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1(lean_object* v_a_636_, lean_object* v_m_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___y_640_; size_t v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v_size_646_; lean_object* v_buckets_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_692_; 
v_size_646_ = lean_ctor_get(v_m_637_, 0);
v_buckets_647_ = lean_ctor_get(v_m_637_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_m_637_);
if (v_isSharedCheck_692_ == 0)
{
v___x_649_ = v_m_637_;
v_isShared_650_ = v_isSharedCheck_692_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_buckets_647_);
lean_inc(v_size_646_);
lean_dec(v_m_637_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_692_;
goto v_resetjp_648_;
}
v___jp_639_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_array_uset(v___y_640_, v___y_641_, v___y_642_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v___y_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
return v___x_645_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; uint64_t v___y_653_; 
v___x_651_ = lean_array_get_size(v_buckets_647_);
if (lean_obj_tag(v_a_638_) == 0)
{
uint64_t v___x_690_; 
v___x_690_ = 1723ULL;
v___y_653_ = v___x_690_;
goto v___jp_652_;
}
else
{
uint64_t v_hash_691_; 
v_hash_691_ = lean_ctor_get_uint64(v_a_638_, sizeof(void*)*2);
v___y_653_ = v_hash_691_;
goto v___jp_652_;
}
v___jp_652_:
{
uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v_fold_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v_bkt_665_; uint8_t v___x_666_; 
v___x_654_ = 32ULL;
v___x_655_ = lean_uint64_shift_right(v___y_653_, v___x_654_);
v_fold_656_ = lean_uint64_xor(v___y_653_, v___x_655_);
v___x_657_ = 16ULL;
v___x_658_ = lean_uint64_shift_right(v_fold_656_, v___x_657_);
v___x_659_ = lean_uint64_xor(v_fold_656_, v___x_658_);
v___x_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = lean_usize_of_nat(v___x_651_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_sub(v___x_661_, v___x_662_);
v___x_664_ = lean_usize_land(v___x_660_, v___x_663_);
v_bkt_665_ = lean_array_uget_borrowed(v_buckets_647_, v___x_664_);
v___x_666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_638_, v_bkt_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v_size_x27_668_; lean_object* v___x_669_; lean_object* v_buckets_x27_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v_size_x27_668_ = lean_nat_add(v_size_646_, v___x_667_);
lean_dec(v_size_646_);
lean_inc(v_bkt_665_);
v___x_669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_669_, 0, v_a_638_);
lean_ctor_set(v___x_669_, 1, v_a_636_);
lean_ctor_set(v___x_669_, 2, v_bkt_665_);
v_buckets_x27_670_ = lean_array_uset(v_buckets_647_, v___x_664_, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(4u);
v___x_672_ = lean_nat_mul(v_size_x27_668_, v___x_671_);
v___x_673_ = lean_unsigned_to_nat(3u);
v___x_674_ = lean_nat_div(v___x_672_, v___x_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_array_get_size(v_buckets_x27_670_);
v___x_676_ = lean_nat_dec_le(v___x_674_, v___x_675_);
lean_dec(v___x_674_);
if (v___x_676_ == 0)
{
lean_object* v_val_677_; lean_object* v___x_679_; 
v_val_677_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1_spec__4___redArg(v_buckets_x27_670_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_val_677_);
lean_ctor_set(v___x_649_, 0, v_size_x27_668_);
v___x_679_ = v___x_649_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_size_x27_668_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_val_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
else
{
lean_object* v___x_682_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_buckets_x27_670_);
lean_ctor_set(v___x_649_, 0, v_size_x27_668_);
v___x_682_ = v___x_649_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_size_x27_668_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_buckets_x27_670_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
lean_object* v___x_684_; lean_object* v_buckets_x27_685_; lean_object* v_bkt_x27_686_; uint8_t v___x_687_; 
lean_inc(v_bkt_665_);
lean_del_object(v___x_649_);
v___x_684_ = lean_box(0);
v_buckets_x27_685_ = lean_array_uset(v_buckets_647_, v___x_664_, v___x_684_);
lean_inc(v_a_638_);
v_bkt_x27_686_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1_spec__2(v_a_636_, v_a_638_, v_bkt_665_);
v___x_687_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__0_spec__0___redArg(v_a_638_, v_bkt_x27_686_);
lean_dec(v_a_638_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_sub(v_size_646_, v___x_688_);
lean_dec(v_size_646_);
v___y_640_ = v_buckets_x27_685_;
v___y_641_ = v___x_664_;
v___y_642_ = v_bkt_x27_686_;
v___y_643_ = v___x_689_;
goto v___jp_639_;
}
else
{
v___y_640_ = v_buckets_x27_685_;
v___y_641_ = v___x_664_;
v___y_642_ = v_bkt_x27_686_;
v___y_643_ = v_size_646_;
goto v___jp_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___lam__0(lean_object* v_a_693_, lean_object* v_constMap_694_, lean_object* v___x_695_, lean_object* v_ref_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = lean_name_eq(v_ref_696_, v_a_693_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_694_, v_ref_696_);
if (lean_obj_tag(v___x_699_) == 1)
{
lean_object* v_val_700_; 
v_val_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v___x_699_, 1);
if (lean_obj_tag(v_val_700_) == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec_ref_known(v_val_700_, 1);
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lake_Check_usedAxioms_spec__1(v_a_693_, v___y_697_, v_ref_696_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_695_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; 
lean_dec(v_val_700_);
lean_dec(v_ref_696_);
lean_dec(v_a_693_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_695_);
lean_ctor_set(v___x_703_, 1, v___y_697_);
return v___x_703_;
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v___x_699_);
lean_dec(v_ref_696_);
lean_dec(v_a_693_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_695_);
lean_ctor_set(v___x_704_, 1, v___y_697_);
return v___x_704_;
}
}
else
{
lean_object* v___x_705_; 
lean_dec(v_ref_696_);
lean_dec(v_a_693_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_695_);
lean_ctor_set(v___x_705_, 1, v___y_697_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___lam__0___boxed(lean_object* v_a_706_, lean_object* v_constMap_707_, lean_object* v___x_708_, lean_object* v_ref_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___lam__0(v_a_706_, v_constMap_707_, v___x_708_, v_ref_709_, v___y_710_);
lean_dec_ref(v_constMap_707_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3(lean_object* v_env_712_, lean_object* v_as_713_, size_t v_sz_714_, size_t v_i_715_, lean_object* v_b_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_a_719_; lean_object* v_snd_720_; uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_715_, v_sz_714_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v_env_712_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_b_716_);
lean_ctor_set(v___x_725_, 1, v___y_717_);
return v___x_725_;
}
else
{
lean_object* v_constMap_726_; lean_object* v___x_727_; lean_object* v_a_728_; lean_object* v___x_729_; 
v_constMap_726_ = lean_ctor_get(v_env_712_, 0);
v___x_727_ = lean_box(0);
v_a_728_ = lean_array_uget_borrowed(v_as_713_, v_i_715_);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_726_, v_a_728_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_val_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v_snd_733_; 
v_val_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v___x_729_, 1);
lean_inc_ref(v_constMap_726_);
lean_inc(v_a_728_);
v___f_731_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___lam__0___boxed), 5, 3);
lean_closure_set(v___f_731_, 0, v_a_728_);
lean_closure_set(v___f_731_, 1, v_constMap_726_);
lean_closure_set(v___f_731_, 2, v___x_727_);
v___x_732_ = l_Lake_Check_runForUsedConsts___at___00Lake_Check_usedAxioms_spec__2(v_val_730_, v___f_731_, v___y_717_);
v_snd_733_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_snd_733_);
lean_dec_ref(v___x_732_);
v_a_719_ = v___x_727_;
v_snd_720_ = v_snd_733_;
goto v___jp_718_;
}
else
{
lean_dec(v___x_729_);
v_a_719_ = v___x_727_;
v_snd_720_ = v___y_717_;
goto v___jp_718_;
}
}
v___jp_718_:
{
size_t v___x_721_; size_t v___x_722_; 
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_715_, v___x_721_);
v_i_715_ = v___x_722_;
v_b_716_ = v_a_719_;
v___y_717_ = v_snd_720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3___boxed(lean_object* v_env_734_, lean_object* v_as_735_, lean_object* v_sz_736_, lean_object* v_i_737_, lean_object* v_b_738_, lean_object* v___y_739_){
_start:
{
size_t v_sz_boxed_740_; size_t v_i_boxed_741_; lean_object* v_res_742_; 
v_sz_boxed_740_ = lean_unbox_usize(v_sz_736_);
lean_dec(v_sz_736_);
v_i_boxed_741_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3(v_env_734_, v_as_735_, v_sz_boxed_740_, v_i_boxed_741_, v_b_738_, v___y_739_);
lean_dec_ref(v_as_735_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Check_usedAxioms_spec__4(lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
return v_x_743_;
}
else
{
lean_object* v_key_745_; lean_object* v_value_746_; lean_object* v_tail_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_key_745_ = lean_ctor_get(v_x_744_, 0);
v_value_746_ = lean_ctor_get(v_x_744_, 1);
v_tail_747_ = lean_ctor_get(v_x_744_, 2);
lean_inc(v_value_746_);
lean_inc(v_key_745_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_key_745_);
lean_ctor_set(v___x_748_, 1, v_value_746_);
v___x_749_ = lean_array_push(v_x_743_, v___x_748_);
v_x_743_ = v___x_749_;
v_x_744_ = v_tail_747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Check_usedAxioms_spec__4___boxed(lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Check_usedAxioms_spec__4(v_x_751_, v_x_752_);
lean_dec(v_x_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_usedAxioms_spec__5(lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, lean_object* v_b_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; 
v___x_759_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
v___x_760_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lake_Check_usedAxioms_spec__4(v_b_757_, v___x_759_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_755_, v___x_761_);
v_i_755_ = v___x_762_;
v_b_757_ = v___x_760_;
goto _start;
}
else
{
return v_b_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_usedAxioms_spec__5___boxed(lean_object* v_as_764_, lean_object* v_i_765_, lean_object* v_stop_766_, lean_object* v_b_767_){
_start:
{
size_t v_i_boxed_768_; size_t v_stop_boxed_769_; lean_object* v_res_770_; 
v_i_boxed_768_ = lean_unbox_usize(v_i_765_);
lean_dec(v_i_765_);
v_stop_boxed_769_ = lean_unbox_usize(v_stop_766_);
lean_dec(v_stop_766_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_usedAxioms_spec__5(v_as_764_, v_i_boxed_768_, v_stop_boxed_769_, v_b_767_);
lean_dec_ref(v_as_764_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg(lean_object* v_hi_771_, lean_object* v_pivot_772_, lean_object* v_as_773_, lean_object* v_i_774_, lean_object* v_k_775_){
_start:
{
uint8_t v___x_776_; 
v___x_776_ = lean_nat_dec_lt(v_k_775_, v_hi_771_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec(v_k_775_);
v___x_777_ = lean_array_fswap(v_as_773_, v_i_774_, v_hi_771_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_i_774_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; lean_object* v_fst_780_; lean_object* v_fst_781_; uint8_t v___x_782_; 
v___x_779_ = lean_array_fget_borrowed(v_as_773_, v_k_775_);
v_fst_780_ = lean_ctor_get(v___x_779_, 0);
v_fst_781_ = lean_ctor_get(v_pivot_772_, 0);
v___x_782_ = l_Lean_Name_lt(v_fst_780_, v_fst_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_k_775_, v___x_783_);
lean_dec(v_k_775_);
v_k_775_ = v___x_784_;
goto _start;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_array_fswap(v_as_773_, v_i_774_, v_k_775_);
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_i_774_, v___x_787_);
lean_dec(v_i_774_);
v___x_789_ = lean_nat_add(v_k_775_, v___x_787_);
lean_dec(v_k_775_);
v_as_773_ = v___x_786_;
v_i_774_ = v___x_788_;
v_k_775_ = v___x_789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg___boxed(lean_object* v_hi_791_, lean_object* v_pivot_792_, lean_object* v_as_793_, lean_object* v_i_794_, lean_object* v_k_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg(v_hi_791_, v_pivot_792_, v_as_793_, v_i_794_, v_k_795_);
lean_dec_ref(v_pivot_792_);
lean_dec(v_hi_791_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0(lean_object* v_x1_797_, lean_object* v_x2_798_){
_start:
{
lean_object* v_fst_799_; lean_object* v_fst_800_; uint8_t v___x_801_; 
v_fst_799_ = lean_ctor_get(v_x1_797_, 0);
v_fst_800_ = lean_ctor_get(v_x2_798_, 0);
v___x_801_ = l_Lean_Name_lt(v_fst_799_, v_fst_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0___boxed(lean_object* v_x1_802_, lean_object* v_x2_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0(v_x1_802_, v_x2_803_);
lean_dec_ref(v_x2_803_);
lean_dec_ref(v_x1_802_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(lean_object* v_n_806_, lean_object* v_as_807_, lean_object* v_lo_808_, lean_object* v_hi_809_){
_start:
{
lean_object* v___y_811_; uint8_t v___x_821_; 
v___x_821_ = lean_nat_dec_lt(v_lo_808_, v_hi_809_);
if (v___x_821_ == 0)
{
lean_dec(v_lo_808_);
return v_as_807_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_mid_824_; lean_object* v___y_826_; lean_object* v___y_832_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_822_ = lean_nat_add(v_lo_808_, v_hi_809_);
v___x_823_ = lean_unsigned_to_nat(1u);
v_mid_824_ = lean_nat_shiftr(v___x_822_, v___x_823_);
lean_dec(v___x_822_);
v___x_837_ = lean_array_fget_borrowed(v_as_807_, v_mid_824_);
v___x_838_ = lean_array_fget_borrowed(v_as_807_, v_lo_808_);
v___x_839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
v___y_832_ = v_as_807_;
goto v___jp_831_;
}
else
{
lean_object* v___x_840_; 
v___x_840_ = lean_array_fswap(v_as_807_, v_lo_808_, v_mid_824_);
v___y_832_ = v___x_840_;
goto v___jp_831_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_array_fget_borrowed(v___y_826_, v_mid_824_);
v___x_828_ = lean_array_fget_borrowed(v___y_826_, v_hi_809_);
v___x_829_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0(v___x_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_dec(v_mid_824_);
v___y_811_ = v___y_826_;
goto v___jp_810_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_array_fswap(v___y_826_, v_mid_824_, v_hi_809_);
lean_dec(v_mid_824_);
v___y_811_ = v___x_830_;
goto v___jp_810_;
}
}
v___jp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_array_fget_borrowed(v___y_832_, v_hi_809_);
v___x_834_ = lean_array_fget_borrowed(v___y_832_, v_lo_808_);
v___x_835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___lam__0(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
v___y_826_ = v___y_832_;
goto v___jp_825_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = lean_array_fswap(v___y_832_, v_lo_808_, v_hi_809_);
v___y_826_ = v___x_836_;
goto v___jp_825_;
}
}
}
v___jp_810_:
{
lean_object* v_pivot_812_; lean_object* v___x_813_; lean_object* v_fst_814_; lean_object* v_snd_815_; uint8_t v___x_816_; 
v_pivot_812_ = lean_array_fget(v___y_811_, v_hi_809_);
lean_inc_n(v_lo_808_, 2);
v___x_813_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg(v_hi_809_, v_pivot_812_, v___y_811_, v_lo_808_, v_lo_808_);
lean_dec(v_pivot_812_);
v_fst_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_fst_814_);
v_snd_815_ = lean_ctor_get(v___x_813_, 1);
lean_inc(v_snd_815_);
lean_dec_ref(v___x_813_);
v___x_816_ = lean_nat_dec_le(v_hi_809_, v_fst_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(v_n_806_, v_snd_815_, v_lo_808_, v_fst_814_);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_add(v_fst_814_, v___x_818_);
lean_dec(v_fst_814_);
v_as_807_ = v___x_817_;
v_lo_808_ = v___x_819_;
goto _start;
}
else
{
lean_dec(v_fst_814_);
lean_dec(v_lo_808_);
return v_snd_815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg___boxed(lean_object* v_n_841_, lean_object* v_as_842_, lean_object* v_lo_843_, lean_object* v_hi_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(v_n_841_, v_as_842_, v_lo_843_, v_hi_844_);
lean_dec(v_hi_844_);
lean_dec(v_n_841_);
return v_res_845_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__0(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = lean_box(0);
v___x_847_ = lean_unsigned_to_nat(16u);
v___x_848_ = lean_mk_array(v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l_Lake_Check_usedAxioms___closed__1(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__0, &l_Lake_Check_usedAxioms___closed__0_once, _init_l_Lake_Check_usedAxioms___closed__0);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_usedAxioms(lean_object* v_env_852_){
_start:
{
lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_862_; lean_object* v_constOrder_869_; lean_object* v___x_870_; size_t v_sz_871_; size_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_snd_876_; lean_object* v_size_877_; lean_object* v_buckets_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_constOrder_869_ = lean_ctor_get(v_env_852_, 1);
lean_inc_ref(v_constOrder_869_);
v___x_870_ = lean_box(0);
v_sz_871_ = lean_array_size(v_constOrder_869_);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_usedAxioms_spec__3(v_env_852_, v_constOrder_869_, v_sz_871_, v___x_872_, v___x_870_, v___x_874_);
lean_dec_ref(v_constOrder_869_);
v_snd_876_ = lean_ctor_get(v___x_875_, 1);
lean_inc(v_snd_876_);
lean_dec_ref(v___x_875_);
v_size_877_ = lean_ctor_get(v_snd_876_, 0);
lean_inc(v_size_877_);
v_buckets_878_ = lean_ctor_get(v_snd_876_, 1);
lean_inc_ref(v_buckets_878_);
lean_dec(v_snd_876_);
v___x_879_ = lean_mk_empty_array_with_capacity(v_size_877_);
lean_dec(v_size_877_);
v___x_880_ = lean_array_get_size(v_buckets_878_);
v___x_881_ = lean_nat_dec_lt(v___x_873_, v___x_880_);
if (v___x_881_ == 0)
{
lean_dec_ref(v_buckets_878_);
v___y_862_ = v___x_879_;
goto v___jp_861_;
}
else
{
size_t v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_usize_of_nat(v___x_880_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Check_usedAxioms_spec__5(v_buckets_878_, v___x_872_, v___x_882_, v___x_879_);
lean_dec_ref(v_buckets_878_);
v___y_862_ = v___x_883_;
goto v___jp_861_;
}
v___jp_853_:
{
uint8_t v___x_858_; 
v___x_858_ = lean_nat_dec_le(v___y_857_, v___y_855_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
lean_dec(v___y_855_);
lean_inc(v___y_857_);
v___x_859_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(v___y_854_, v___y_856_, v___y_857_, v___y_857_);
lean_dec(v___y_857_);
lean_dec(v___y_854_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; 
v___x_860_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(v___y_854_, v___y_856_, v___y_857_, v___y_855_);
lean_dec(v___y_855_);
lean_dec(v___y_854_);
return v___x_860_;
}
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_863_ = lean_array_get_size(v___y_862_);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_nat_dec_eq(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_sub(v___x_863_, v___x_866_);
v___x_868_ = lean_nat_dec_le(v___x_864_, v___x_867_);
if (v___x_868_ == 0)
{
lean_inc(v___x_867_);
v___y_854_ = v___x_863_;
v___y_855_ = v___x_867_;
v___y_856_ = v___y_862_;
v___y_857_ = v___x_867_;
goto v___jp_853_;
}
else
{
v___y_854_ = v___x_863_;
v___y_855_ = v___x_867_;
v___y_856_ = v___y_862_;
v___y_857_ = v___x_864_;
goto v___jp_853_;
}
}
else
{
return v___y_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0(lean_object* v_n_884_, lean_object* v_as_885_, lean_object* v_lo_886_, lean_object* v_hi_887_, lean_object* v_w_888_, lean_object* v_hlo_889_, lean_object* v_hhi_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___redArg(v_n_884_, v_as_885_, v_lo_886_, v_hi_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0___boxed(lean_object* v_n_892_, lean_object* v_as_893_, lean_object* v_lo_894_, lean_object* v_hi_895_, lean_object* v_w_896_, lean_object* v_hlo_897_, lean_object* v_hhi_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0(v_n_892_, v_as_893_, v_lo_894_, v_hi_895_, v_w_896_, v_hlo_897_, v_hhi_898_);
lean_dec(v_hi_895_);
lean_dec(v_n_892_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0(lean_object* v_n_900_, lean_object* v_lo_901_, lean_object* v_hi_902_, lean_object* v_hhi_903_, lean_object* v_pivot_904_, lean_object* v_as_905_, lean_object* v_i_906_, lean_object* v_k_907_, lean_object* v_ilo_908_, lean_object* v_ik_909_, lean_object* v_w_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___redArg(v_hi_902_, v_pivot_904_, v_as_905_, v_i_906_, v_k_907_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0___boxed(lean_object* v_n_912_, lean_object* v_lo_913_, lean_object* v_hi_914_, lean_object* v_hhi_915_, lean_object* v_pivot_916_, lean_object* v_as_917_, lean_object* v_i_918_, lean_object* v_k_919_, lean_object* v_ilo_920_, lean_object* v_ik_921_, lean_object* v_w_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lake_Check_usedAxioms_spec__0_spec__0(v_n_912_, v_lo_913_, v_hi_914_, v_hhi_915_, v_pivot_916_, v_as_917_, v_i_918_, v_k_919_, v_ilo_920_, v_ik_921_, v_w_922_);
lean_dec_ref(v_pivot_916_);
lean_dec(v_hi_914_);
lean_dec(v_lo_913_);
lean_dec(v_n_912_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(lean_object* v_as_924_, size_t v_sz_925_, size_t v_i_926_, lean_object* v_b_927_){
_start:
{
uint8_t v___x_928_; 
v___x_928_ = lean_usize_dec_lt(v_i_926_, v_sz_925_);
if (v___x_928_ == 0)
{
return v_b_927_;
}
else
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v_r_931_; size_t v___x_932_; size_t v___x_933_; 
v_a_929_ = lean_array_uget_borrowed(v_as_924_, v_i_926_);
v___x_930_ = lean_box(0);
lean_inc(v_a_929_);
v_r_931_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_spec__1___redArg(v_b_927_, v_a_929_, v___x_930_);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_926_, v___x_932_);
v_i_926_ = v___x_933_;
v_b_927_ = v_r_931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2___boxed(lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_){
_start:
{
size_t v_sz_boxed_939_; size_t v_i_boxed_940_; lean_object* v_res_941_; 
v_sz_boxed_939_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_940_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_as_935_, v_sz_boxed_939_, v_i_boxed_940_, v_b_938_);
lean_dec_ref(v_as_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(lean_object* v_m_942_, lean_object* v_l_943_){
_start:
{
size_t v_sz_944_; size_t v___x_945_; lean_object* v___x_946_; 
v_sz_944_ = lean_array_size(v_l_943_);
v___x_945_ = ((size_t)0ULL);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2_spec__2(v_l_943_, v_sz_944_, v___x_945_, v_m_942_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2___boxed(lean_object* v_m_947_, lean_object* v_l_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v_m_947_, v_l_948_);
lean_dec_ref(v_l_948_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(lean_object* v_solution_952_, lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v_b_956_);
return v___x_958_;
}
else
{
lean_object* v_constMap_959_; lean_object* v_a_960_; lean_object* v___x_961_; 
v_constMap_959_ = lean_ctor_get(v_solution_952_, 0);
v_a_960_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_959_, v_a_960_);
if (lean_obj_tag(v___x_961_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_981_; 
v_val_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_981_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_981_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_981_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
if (lean_obj_tag(v_val_962_) == 2)
{
lean_object* v_val_966_; lean_object* v_toConstantVal_967_; lean_object* v_name_968_; lean_object* v___x_969_; size_t v___x_970_; size_t v___x_971_; 
lean_del_object(v___x_964_);
v_val_966_ = lean_ctor_get(v_val_962_, 0);
lean_inc_ref(v_val_966_);
lean_dec_ref_known(v_val_962_, 1);
v_toConstantVal_967_ = lean_ctor_get(v_val_966_, 0);
lean_inc_ref(v_toConstantVal_967_);
lean_dec_ref(v_val_966_);
v_name_968_ = lean_ctor_get(v_toConstantVal_967_, 0);
lean_inc(v_name_968_);
lean_dec_ref(v_toConstantVal_967_);
v___x_969_ = lean_array_push(v_b_956_, v_name_968_);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_955_, v___x_970_);
v_i_955_ = v___x_971_;
v_b_956_ = v___x_969_;
goto _start;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
lean_dec(v_val_962_);
lean_dec_ref(v_b_956_);
v___x_973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__0));
lean_inc(v_a_960_);
v___x_974_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_960_, v___x_957_);
v___x_975_ = lean_string_append(v___x_973_, v___x_974_);
lean_dec_ref(v___x_974_);
v___x_976_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 0);
lean_ctor_set(v___x_964_, 0, v___x_977_);
v___x_979_ = v___x_964_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v___x_961_);
lean_dec_ref(v_b_956_);
v___x_982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_960_);
v___x_983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_960_, v___x_957_);
v___x_984_ = lean_string_append(v___x_982_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
return v___x_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___boxed(lean_object* v_solution_988_, lean_object* v_as_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_b_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_988_, v_as_989_, v_sz_boxed_993_, v_i_boxed_994_, v_b_992_);
lean_dec_ref(v_as_989_);
lean_dec_ref(v_solution_988_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(lean_object* v_solution_997_, lean_object* v_as_998_, size_t v_sz_999_, size_t v_i_1000_, lean_object* v_b_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_lt(v_i_1000_, v_sz_999_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_b_1001_);
return v___x_1003_;
}
else
{
lean_object* v_constMap_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; 
v_constMap_1004_ = lean_ctor_get(v_solution_997_, 0);
v_a_1005_ = lean_array_uget_borrowed(v_as_998_, v_i_1000_);
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst_spec__1___redArg(v_constMap_1004_, v_a_1005_);
if (lean_obj_tag(v___x_1006_) == 1)
{
lean_object* v_val_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1026_; 
v_val_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1026_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_val_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1026_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
if (lean_obj_tag(v_val_1007_) == 1)
{
lean_object* v_val_1011_; lean_object* v_toConstantVal_1012_; lean_object* v_name_1013_; lean_object* v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; 
lean_del_object(v___x_1009_);
v_val_1011_ = lean_ctor_get(v_val_1007_, 0);
lean_inc_ref(v_val_1011_);
lean_dec_ref_known(v_val_1007_, 1);
v_toConstantVal_1012_ = lean_ctor_get(v_val_1011_, 0);
lean_inc_ref(v_toConstantVal_1012_);
lean_dec_ref(v_val_1011_);
v_name_1013_ = lean_ctor_get(v_toConstantVal_1012_, 0);
lean_inc(v_name_1013_);
lean_dec_ref(v_toConstantVal_1012_);
v___x_1014_ = lean_array_push(v_b_1001_, v_name_1013_);
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_add(v_i_1000_, v___x_1015_);
v_i_1000_ = v___x_1016_;
v_b_1001_ = v___x_1014_;
goto _start;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec(v_val_1007_);
lean_dec_ref(v_b_1001_);
v___x_1018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___closed__0));
lean_inc(v_a_1005_);
v___x_1019_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1005_, v___x_1002_);
v___x_1020_ = lean_string_append(v___x_1018_, v___x_1019_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_1022_ = lean_string_append(v___x_1020_, v___x_1021_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1022_);
v___x_1024_ = v___x_1009_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v___x_1006_);
lean_dec_ref(v_b_1001_);
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0___closed__1));
lean_inc(v_a_1005_);
v___x_1028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1005_, v___x_1002_);
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop_validateConst___closed__1));
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1___boxed(lean_object* v_solution_1033_, lean_object* v_as_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_b_1037_){
_start:
{
size_t v_sz_boxed_1038_; size_t v_i_boxed_1039_; lean_object* v_res_1040_; 
v_sz_boxed_1038_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1039_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_1033_, v_as_1034_, v_sz_boxed_1038_, v_i_boxed_1039_, v_b_1037_);
lean_dec_ref(v_as_1034_);
lean_dec_ref(v_solution_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms(lean_object* v_solution_1043_, lean_object* v_theoremTargets_1044_, lean_object* v_definitionTargets_1045_, lean_object* v_legalAxioms_1046_){
_start:
{
lean_object* v_worklist_1047_; size_t v_sz_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_worklist_1047_ = ((lean_object*)(l_Lake_Check_checkAxioms___closed__0));
v_sz_1048_ = lean_array_size(v_theoremTargets_1044_);
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__0(v_solution_1043_, v_theoremTargets_1044_, v_sz_1048_, v___x_1049_, v_worklist_1047_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_solution_1043_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_object* v_a_1059_; size_t v_sz_1060_; lean_object* v___x_1061_; 
v_a_1059_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1050_, 1);
v_sz_1060_ = lean_array_size(v_definitionTargets_1045_);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Check_checkAxioms_spec__1(v_solution_1043_, v_definitionTargets_1045_, v_sz_1060_, v___x_1049_, v_a_1059_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_solution_1043_);
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1070_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1071_ = lean_obj_once(&l_Lake_Check_usedAxioms___closed__1, &l_Lake_Check_usedAxioms___closed__1_once, _init_l_Lake_Check_usedAxioms___closed__1);
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lake_Check_checkAxioms_spec__2(v___x_1071_, v_legalAxioms_1046_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_solution_1043_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1070_);
lean_ctor_set(v___x_1074_, 1, v___x_1071_);
v___x_1075_ = l___private_Lake_Check_Axioms_0__Lake_Check_Axioms_loop(v___x_1073_, v___x_1074_);
lean_dec_ref_known(v___x_1073_, 2);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1092_; 
v_a_1084_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1086_ = v___x_1075_;
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1075_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1092_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_fst_1088_; lean_object* v___x_1090_; 
v_fst_1088_ = lean_ctor_get(v_a_1084_, 0);
lean_inc(v_fst_1088_);
lean_dec(v_a_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v_fst_1088_);
v___x_1090_ = v___x_1086_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_fst_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Check_checkAxioms___boxed(lean_object* v_solution_1093_, lean_object* v_theoremTargets_1094_, lean_object* v_definitionTargets_1095_, lean_object* v_legalAxioms_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lake_Check_checkAxioms(v_solution_1093_, v_theoremTargets_1094_, v_definitionTargets_1095_, v_legalAxioms_1096_);
lean_dec_ref(v_legalAxioms_1096_);
lean_dec_ref(v_definitionTargets_1095_);
lean_dec_ref(v_theoremTargets_1094_);
return v_res_1097_;
}
}
lean_object* runtime_initialize_LeanExport_Parse(uint8_t builtin);
lean_object* runtime_initialize_Lake_Check_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Name(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Name(builtin);
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
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
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
res = initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
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
