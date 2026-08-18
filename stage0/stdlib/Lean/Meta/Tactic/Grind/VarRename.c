// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.VarRename
// Imports: public import Init.Data.Array.QSort public import Std.Data.HashSet public import Init.Data.Hashable
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instAndThenVarCollector___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instAndThenVarCollector = (const lean_object*)&l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__7_value),((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__4_value),((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_collectMapVars___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__8_value),((lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__6_value)}};
static const lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_collectMapVars___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar = (const lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_nat_dec_eq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
v___x_62_ = lean_uint64_of_nat(v_query_59_);
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___x_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___x_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_usize_to_nat(v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg(lean_object* v_b_80_, lean_object* v_acc_81_, lean_object* v_i_82_){
_start:
{
lean_object* v___y_84_; lean_object* v_keyArray_92_; lean_object* v_valueArray_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_keyArray_92_ = lean_ctor_get(v_b_80_, 1);
v_valueArray_93_ = lean_ctor_get(v_b_80_, 2);
v___x_94_ = lean_array_get_size(v_keyArray_92_);
v___x_95_ = lean_nat_dec_lt(v_i_82_, v___x_94_);
if (v___x_95_ == 0)
{
lean_dec(v_i_82_);
return v_acc_81_;
}
else
{
lean_object* v___x_96_; uint8_t v_isSome_97_; 
v___x_96_ = lean_array_fget_borrowed(v_keyArray_92_, v_i_82_);
v_isSome_97_ = lean_noption_is_some(v___x_96_);
if (v_isSome_97_ == 0)
{
goto v___jp_88_;
}
else
{
lean_object* v___x_98_; uint8_t v_isSome_99_; 
v___x_98_ = lean_array_fget_borrowed(v_valueArray_93_, v_i_82_);
v_isSome_99_ = lean_noption_is_some(v___x_98_);
if (v_isSome_99_ == 0)
{
goto v___jp_88_;
}
else
{
lean_object* v_val_100_; lean_object* v_val_101_; lean_object* v_i_103_; lean_object* v___x_108_; 
lean_inc(v___x_96_);
v_val_100_ = lean_noption_get(v___x_96_);
lean_inc(v___x_98_);
v_val_101_ = lean_noption_get(v___x_98_);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_acc_81_, v_val_100_);
switch(lean_obj_tag(v___x_108_))
{
case 0:
{
lean_object* v_index_109_; lean_object* v_size_110_; lean_object* v___x_111_; 
v_index_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_index_109_);
lean_dec_ref_known(v___x_108_, 3);
v_size_110_ = lean_ctor_get(v_acc_81_, 0);
lean_inc(v_size_110_);
v___x_111_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_81_, v_size_110_, v_index_109_, v_val_100_, v_val_101_);
lean_dec(v_index_109_);
v___y_84_ = v___x_111_;
goto v___jp_83_;
}
case 1:
{
lean_object* v_index_112_; 
v_index_112_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_index_112_);
lean_dec_ref_known(v___x_108_, 1);
v_i_103_ = v_index_112_;
goto v___jp_102_;
}
default: 
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_81_, v___x_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_index_115_; 
v_index_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_index_115_);
lean_dec_ref_known(v___x_114_, 1);
v_i_103_ = v_index_115_;
goto v___jp_102_;
}
else
{
lean_dec(v_val_101_);
lean_dec(v_val_100_);
v___y_84_ = v_acc_81_;
goto v___jp_83_;
}
}
}
v___jp_102_:
{
lean_object* v_size_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_size_104_ = lean_ctor_get(v_acc_81_, 0);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_size_104_, v___x_105_);
v___x_107_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_81_, v___x_106_, v_i_103_, v_val_100_, v_val_101_);
lean_dec(v_i_103_);
v___y_84_ = v___x_107_;
goto v___jp_83_;
}
}
}
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_82_, v___x_85_);
lean_dec(v_i_82_);
v_acc_81_ = v___y_84_;
v_i_82_ = v___x_86_;
goto _start;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_i_82_, v___x_89_);
lean_dec(v_i_82_);
v_i_82_ = v___x_90_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_116_, lean_object* v_acc_117_, lean_object* v_i_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg(v_b_116_, v_acc_117_, v_i_118_);
lean_dec_ref(v_b_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg(lean_object* v_init_120_, lean_object* v_b_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg(v_b_121_, v_init_120_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg___boxed(lean_object* v_init_124_, lean_object* v_b_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg(v_init_124_, v_b_125_);
lean_dec_ref(v_b_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(lean_object* v_m_127_){
_start:
{
lean_object* v_keyArray_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_cellCount_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_target_135_; lean_object* v___x_136_; 
v_keyArray_128_ = lean_ctor_get(v_m_127_, 1);
v___x_129_ = lean_array_get_size(v_keyArray_128_);
v___x_130_ = lean_unsigned_to_nat(2u);
v_cellCount_131_ = lean_nat_mul(v___x_129_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_131_);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_131_);
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_131_);
v_target_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_135_, 0, v___x_132_);
lean_ctor_set(v_target_135_, 1, v___x_133_);
lean_ctor_set(v_target_135_, 2, v___x_134_);
v___x_136_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg(v_target_135_, v_m_127_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg___boxed(lean_object* v_m_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_m_137_);
lean_dec_ref(v_m_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectVar(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___y_143_; lean_object* v_i_144_; lean_object* v___y_150_; lean_object* v___y_160_; lean_object* v_i_161_; lean_object* v___x_176_; 
v___x_141_ = lean_box(0);
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_x_140_, v_x_139_);
switch(lean_obj_tag(v___x_176_))
{
case 0:
{
lean_dec_ref_known(v___x_176_, 3);
lean_dec(v_x_139_);
return v_x_140_;
}
case 1:
{
lean_object* v_index_177_; lean_object* v_size_178_; lean_object* v_keyArray_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_index_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_177_);
lean_dec_ref_known(v___x_176_, 1);
v_size_178_ = lean_ctor_get(v_x_140_, 0);
v_keyArray_179_ = lean_ctor_get(v_x_140_, 1);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_size_178_, v___x_180_);
v___x_182_ = lean_array_get_size(v_keyArray_179_);
v___x_183_ = lean_nat_dec_lt(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_dec(v___x_181_);
lean_dec(v_index_177_);
goto v___jp_166_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_184_ = lean_unsigned_to_nat(4u);
v___x_185_ = lean_nat_mul(v___x_181_, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(3u);
v___x_187_ = lean_nat_mul(v___x_182_, v___x_186_);
v___x_188_ = lean_nat_dec_le(v___x_185_, v___x_187_);
lean_dec(v___x_187_);
lean_dec(v___x_185_);
if (v___x_188_ == 0)
{
lean_dec(v___x_181_);
lean_dec(v_index_177_);
goto v___jp_166_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_140_, v___x_181_, v_index_177_, v_x_139_, v___x_141_);
lean_dec(v_index_177_);
return v___x_189_;
}
}
}
default: 
{
lean_object* v_size_190_; lean_object* v_keyArray_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_size_190_ = lean_ctor_get(v_x_140_, 0);
v_keyArray_191_ = lean_ctor_get(v_x_140_, 1);
v___x_192_ = lean_unsigned_to_nat(1u);
v___x_193_ = lean_nat_add(v_size_190_, v___x_192_);
v___x_194_ = lean_array_get_size(v_keyArray_191_);
v___x_195_ = lean_nat_dec_lt(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
lean_dec(v___x_193_);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_x_140_);
lean_dec_ref(v_x_140_);
v___y_150_ = v___x_196_;
goto v___jp_149_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_197_ = lean_unsigned_to_nat(4u);
v___x_198_ = lean_nat_mul(v___x_193_, v___x_197_);
lean_dec(v___x_193_);
v___x_199_ = lean_unsigned_to_nat(3u);
v___x_200_ = lean_nat_mul(v___x_194_, v___x_199_);
v___x_201_ = lean_nat_dec_le(v___x_198_, v___x_200_);
lean_dec(v___x_200_);
lean_dec(v___x_198_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_x_140_);
lean_dec_ref(v_x_140_);
v___y_150_ = v___x_202_;
goto v___jp_149_;
}
else
{
v___y_150_ = v_x_140_;
goto v___jp_149_;
}
}
}
}
v___jp_142_:
{
lean_object* v_size_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_size_145_ = lean_ctor_get(v___y_143_, 0);
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_add(v_size_145_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_143_, v___x_147_, v_i_144_, v_x_139_, v___x_141_);
lean_dec(v_i_144_);
return v___x_148_;
}
v___jp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v___y_150_, v_x_139_);
switch(lean_obj_tag(v___x_151_))
{
case 0:
{
lean_object* v_index_152_; lean_object* v_size_153_; lean_object* v___x_154_; 
v_index_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_index_152_);
lean_dec_ref_known(v___x_151_, 3);
v_size_153_ = lean_ctor_get(v___y_150_, 0);
lean_inc(v_size_153_);
v___x_154_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_150_, v_size_153_, v_index_152_, v_x_139_, v___x_141_);
lean_dec(v_index_152_);
return v___x_154_;
}
case 1:
{
lean_object* v_index_155_; 
v_index_155_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_index_155_);
lean_dec_ref_known(v___x_151_, 1);
v___y_143_ = v___y_150_;
v_i_144_ = v_index_155_;
goto v___jp_142_;
}
default: 
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_150_, v___x_156_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_index_158_; 
v_index_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_index_158_);
lean_dec_ref_known(v___x_157_, 1);
v___y_143_ = v___y_150_;
v_i_144_ = v_index_158_;
goto v___jp_142_;
}
else
{
lean_dec(v_x_139_);
return v___y_150_;
}
}
}
}
v___jp_159_:
{
lean_object* v_size_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_size_162_ = lean_ctor_get(v___y_160_, 0);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_size_162_, v___x_163_);
v___x_165_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_160_, v___x_164_, v_i_161_, v_x_139_, v___x_141_);
lean_dec(v_i_161_);
return v___x_165_;
}
v___jp_166_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_x_140_);
lean_dec_ref(v_x_140_);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v___x_167_, v_x_139_);
switch(lean_obj_tag(v___x_168_))
{
case 0:
{
lean_object* v_index_169_; lean_object* v_size_170_; lean_object* v___x_171_; 
v_index_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_index_169_);
lean_dec_ref_known(v___x_168_, 3);
v_size_170_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_size_170_);
v___x_171_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_167_, v_size_170_, v_index_169_, v_x_139_, v___x_141_);
lean_dec(v_index_169_);
return v___x_171_;
}
case 1:
{
lean_object* v_index_172_; 
v_index_172_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_index_172_);
lean_dec_ref_known(v___x_168_, 1);
v___y_160_ = v___x_167_;
v_i_161_ = v_index_172_;
goto v___jp_159_;
}
default: 
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_167_, v___x_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_index_175_; 
v_index_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_index_175_);
lean_dec_ref_known(v___x_174_, 1);
v___y_160_ = v___x_167_;
v_i_161_ = v_index_175_;
goto v___jp_159_;
}
else
{
lean_dec(v_x_139_);
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0(lean_object* v_00_u03b2_203_, lean_object* v_m_204_, lean_object* v_query_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_m_204_, v_query_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___boxed(lean_object* v_00_u03b2_207_, lean_object* v_m_208_, lean_object* v_query_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0(v_00_u03b2_207_, v_m_208_, v_query_209_);
lean_dec(v_query_209_);
lean_dec_ref(v_m_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1(lean_object* v_00_u03b2_211_, lean_object* v_m_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_m_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___boxed(lean_object* v_00_u03b2_214_, lean_object* v_m_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1(v_00_u03b2_214_, v_m_215_);
lean_dec_ref(v_m_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_object* v_00_u03b2_217_, lean_object* v_m_218_, lean_object* v_query_219_, lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_m_218_, v_query_219_, v_x_220_, v_x_221_, v_x_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_225_, lean_object* v_m_226_, lean_object* v_query_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(v_00_u03b2_225_, v_m_226_, v_query_227_, v_x_228_, v_x_229_, v_x_230_, v_x_231_);
lean_dec(v_query_227_);
lean_dec_ref(v_m_226_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2(lean_object* v_00_u03b2_233_, lean_object* v_init_234_, lean_object* v_b_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___redArg(v_init_234_, v_b_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2___boxed(lean_object* v_00_u03b2_237_, lean_object* v_init_238_, lean_object* v_b_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2(v_00_u03b2_237_, v_init_238_, v_b_239_);
lean_dec_ref(v_b_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_241_, lean_object* v_b_242_, lean_object* v_acc_243_, lean_object* v_i_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___redArg(v_b_242_, v_acc_243_, v_i_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_246_, lean_object* v_b_247_, lean_object* v_acc_248_, lean_object* v_i_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1_spec__2_spec__3(v_00_u03b2_246_, v_b_247_, v_acc_248_, v_i_249_);
lean_dec_ref(v_b_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(lean_object* v_c_u2081_251_, lean_object* v_c_u2082_252_, lean_object* v_s_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_apply_1(v_c_u2081_251_, v_s_253_);
v___x_256_ = lean_apply_2(v_c_u2082_252_, v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(lean_object* v_k_259_, lean_object* v_a_260_, lean_object* v_b_261_, lean_object* v_acc_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_apply_2(v_k_259_, v_a_260_, v_acc_262_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(lean_object* v_k_265_, lean_object* v_a_266_, lean_object* v_b_267_, lean_object* v_acc_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(v_k_265_, v_a_266_, v_b_267_, v_acc_268_);
lean_dec(v_b_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg(lean_object* v_m_289_, lean_object* v_k_290_, lean_object* v_s_291_){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___f_292_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_292_, 0, v_k_290_);
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_collectMapVars___redArg___closed__9));
v___x_294_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_293_, v___f_292_, v_s_291_, v_m_289_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars(lean_object* v_00_u03b1_295_, lean_object* v_Expr_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_m_299_, lean_object* v_k_300_, lean_object* v_s_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_collectMapVars___redArg(v_m_299_, v_k_300_, v_s_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___boxed(lean_object* v_00_u03b1_303_, lean_object* v_Expr_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_m_307_, lean_object* v_k_308_, lean_object* v_s_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Grind_collectMapVars(v_00_u03b1_303_, v_Expr_304_, v_x_305_, v_x_306_, v_m_307_, v_k_308_, v_s_309_);
lean_dec_ref(v_x_306_);
lean_dec_ref(v_x_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(lean_object* v_b_311_, lean_object* v_acc_312_, lean_object* v_i_313_){
_start:
{
lean_object* v_keyArray_318_; lean_object* v_valueArray_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_keyArray_318_ = lean_ctor_get(v_b_311_, 1);
v_valueArray_319_ = lean_ctor_get(v_b_311_, 2);
v___x_320_ = lean_array_get_size(v_keyArray_318_);
v___x_321_ = lean_nat_dec_lt(v_i_313_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec(v_i_313_);
return v_acc_312_;
}
else
{
lean_object* v___x_322_; uint8_t v_isSome_323_; 
v___x_322_ = lean_array_fget_borrowed(v_keyArray_318_, v_i_313_);
v_isSome_323_ = lean_noption_is_some(v___x_322_);
if (v_isSome_323_ == 0)
{
goto v___jp_314_;
}
else
{
lean_object* v___x_324_; uint8_t v_isSome_325_; 
v___x_324_ = lean_array_fget_borrowed(v_valueArray_319_, v_i_313_);
v_isSome_325_ = lean_noption_is_some(v___x_324_);
if (v_isSome_325_ == 0)
{
goto v___jp_314_;
}
else
{
lean_object* v_val_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_inc(v___x_322_);
v_val_326_ = lean_noption_get(v___x_322_);
v___x_327_ = lean_array_push(v_acc_312_, v_val_326_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_i_313_, v___x_328_);
lean_dec(v_i_313_);
v_acc_312_ = v___x_327_;
v_i_313_ = v___x_329_;
goto _start;
}
}
}
v___jp_314_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_i_313_, v___x_315_);
lean_dec(v_i_313_);
v_i_313_ = v___x_316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___boxed(lean_object* v_b_331_, lean_object* v_acc_332_, lean_object* v_i_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(v_b_331_, v_acc_332_, v_i_333_);
lean_dec_ref(v_b_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object* v_init_335_, lean_object* v_b_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(v_b_336_, v_init_335_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object* v_init_339_, lean_object* v_b_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(v_init_339_, v_b_340_);
lean_dec_ref(v_b_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg(lean_object* v_hi_342_, lean_object* v_pivot_343_, lean_object* v_as_344_, lean_object* v_i_345_, lean_object* v_k_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_nat_dec_lt(v_k_346_, v_hi_342_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_k_346_);
v___x_348_ = lean_array_fswap(v_as_344_, v_i_345_, v_hi_342_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_i_345_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_array_fget_borrowed(v_as_344_, v_k_346_);
v___x_351_ = lean_nat_dec_lt(v___x_350_, v_pivot_343_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_k_346_, v___x_352_);
lean_dec(v_k_346_);
v_k_346_ = v___x_353_;
goto _start;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_array_fswap(v_as_344_, v_i_345_, v_k_346_);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_i_345_, v___x_356_);
lean_dec(v_i_345_);
v___x_358_ = lean_nat_add(v_k_346_, v___x_356_);
lean_dec(v_k_346_);
v_as_344_ = v___x_355_;
v_i_345_ = v___x_357_;
v_k_346_ = v___x_358_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg___boxed(lean_object* v_hi_360_, lean_object* v_pivot_361_, lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_k_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg(v_hi_360_, v_pivot_361_, v_as_362_, v_i_363_, v_k_364_);
lean_dec(v_pivot_361_);
lean_dec(v_hi_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(lean_object* v_n_366_, lean_object* v_as_367_, lean_object* v_lo_368_, lean_object* v_hi_369_){
_start:
{
lean_object* v___y_371_; uint8_t v___x_381_; 
v___x_381_ = lean_nat_dec_lt(v_lo_368_, v_hi_369_);
if (v___x_381_ == 0)
{
lean_dec(v_lo_368_);
return v_as_367_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_mid_384_; lean_object* v___y_386_; lean_object* v___y_392_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_382_ = lean_nat_add(v_lo_368_, v_hi_369_);
v___x_383_ = lean_unsigned_to_nat(1u);
v_mid_384_ = lean_nat_shiftr(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
v___x_397_ = lean_array_fget_borrowed(v_as_367_, v_mid_384_);
v___x_398_ = lean_array_fget_borrowed(v_as_367_, v_lo_368_);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
v___y_392_ = v_as_367_;
goto v___jp_391_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_array_fswap(v_as_367_, v_lo_368_, v_mid_384_);
v___y_392_ = v___x_400_;
goto v___jp_391_;
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_387_ = lean_array_fget_borrowed(v___y_386_, v_mid_384_);
v___x_388_ = lean_array_fget_borrowed(v___y_386_, v_hi_369_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_dec(v_mid_384_);
v___y_371_ = v___y_386_;
goto v___jp_370_;
}
else
{
lean_object* v___x_390_; 
v___x_390_ = lean_array_fswap(v___y_386_, v_mid_384_, v_hi_369_);
lean_dec(v_mid_384_);
v___y_371_ = v___x_390_;
goto v___jp_370_;
}
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_array_fget_borrowed(v___y_392_, v_hi_369_);
v___x_394_ = lean_array_fget_borrowed(v___y_392_, v_lo_368_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
if (v___x_395_ == 0)
{
v___y_386_ = v___y_392_;
goto v___jp_385_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_array_fswap(v___y_392_, v_lo_368_, v_hi_369_);
v___y_386_ = v___x_396_;
goto v___jp_385_;
}
}
}
v___jp_370_:
{
lean_object* v_pivot_372_; lean_object* v___x_373_; lean_object* v_fst_374_; lean_object* v_snd_375_; uint8_t v___x_376_; 
v_pivot_372_ = lean_array_fget(v___y_371_, v_hi_369_);
lean_inc_n(v_lo_368_, 2);
v___x_373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg(v_hi_369_, v_pivot_372_, v___y_371_, v_lo_368_, v_lo_368_);
lean_dec(v_pivot_372_);
v_fst_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_fst_374_);
v_snd_375_ = lean_ctor_get(v___x_373_, 1);
lean_inc(v_snd_375_);
lean_dec_ref(v___x_373_);
v___x_376_ = lean_nat_dec_le(v_hi_369_, v_fst_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(v_n_366_, v_snd_375_, v_lo_368_, v_fst_374_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_fst_374_, v___x_378_);
lean_dec(v_fst_374_);
v_as_367_ = v___x_377_;
v_lo_368_ = v___x_379_;
goto _start;
}
else
{
lean_dec(v_fst_374_);
lean_dec(v_lo_368_);
return v_snd_375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg___boxed(lean_object* v_n_401_, lean_object* v_as_402_, lean_object* v_lo_403_, lean_object* v_hi_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(v_n_401_, v_as_402_, v_lo_403_, v_hi_404_);
lean_dec(v_hi_404_);
lean_dec(v_n_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object* v_s_406_){
_start:
{
lean_object* v_size_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_size_407_ = lean_ctor_get(v_s_406_, 0);
v___x_408_ = lean_mk_empty_array_with_capacity(v_size_407_);
v___x_409_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(v___x_408_, v_s_406_);
v___x_410_ = lean_array_get_size(v___x_409_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_nat_dec_eq(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___y_416_; uint8_t v___x_420_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_sub(v___x_410_, v___x_413_);
v___x_420_ = lean_nat_dec_le(v___x_411_, v___x_414_);
if (v___x_420_ == 0)
{
lean_inc(v___x_414_);
v___y_416_ = v___x_414_;
goto v___jp_415_;
}
else
{
v___y_416_ = v___x_411_;
goto v___jp_415_;
}
v___jp_415_:
{
uint8_t v___x_417_; 
v___x_417_ = lean_nat_dec_le(v___y_416_, v___x_414_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec(v___x_414_);
lean_inc(v___y_416_);
v___x_418_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(v___x_410_, v___x_409_, v___y_416_, v___y_416_);
lean_dec(v___y_416_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(v___x_410_, v___x_409_, v___y_416_, v___x_414_);
lean_dec(v___x_414_);
return v___x_419_;
}
}
}
else
{
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Grind_FoundVars_toArray(v_s_421_);
lean_dec_ref(v_s_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(lean_object* v_n_423_, lean_object* v_as_424_, lean_object* v_lo_425_, lean_object* v_hi_426_, lean_object* v_w_427_, lean_object* v_hlo_428_, lean_object* v_hhi_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___redArg(v_n_423_, v_as_424_, v_lo_425_, v_hi_426_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1___boxed(lean_object* v_n_431_, lean_object* v_as_432_, lean_object* v_lo_433_, lean_object* v_hi_434_, lean_object* v_w_435_, lean_object* v_hlo_436_, lean_object* v_hhi_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(v_n_431_, v_as_432_, v_lo_433_, v_hi_434_, v_w_435_, v_hlo_436_, v_hhi_437_);
lean_dec(v_hi_434_);
lean_dec(v_n_431_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2(lean_object* v_n_439_, lean_object* v_lo_440_, lean_object* v_hi_441_, lean_object* v_hhi_442_, lean_object* v_pivot_443_, lean_object* v_as_444_, lean_object* v_i_445_, lean_object* v_k_446_, lean_object* v_ilo_447_, lean_object* v_ik_448_, lean_object* v_w_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___redArg(v_hi_441_, v_pivot_443_, v_as_444_, v_i_445_, v_k_446_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2___boxed(lean_object* v_n_451_, lean_object* v_lo_452_, lean_object* v_hi_453_, lean_object* v_hhi_454_, lean_object* v_pivot_455_, lean_object* v_as_456_, lean_object* v_i_457_, lean_object* v_k_458_, lean_object* v_ilo_459_, lean_object* v_ik_460_, lean_object* v_w_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1_spec__2(v_n_451_, v_lo_452_, v_hi_453_, v_hhi_454_, v_pivot_455_, v_as_456_, v_i_457_, v_k_458_, v_ilo_459_, v_ik_460_, v_w_461_);
lean_dec(v_pivot_455_);
lean_dec(v_hi_453_);
lean_dec(v_lo_452_);
lean_dec(v_n_451_);
return v_res_462_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_463_; lean_object* v___f_464_; 
v___x_463_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_464_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_464_, 0, v___x_463_);
return v___f_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(lean_object* v___f_465_, lean_object* v_s_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; 
v___f_468_ = lean_obj_once(&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0, &l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_468_, v___f_465_, v_s_466_, v_x_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_unsigned_to_nat(0u);
return v___x_470_;
}
else
{
lean_object* v_val_471_; 
v_val_471_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_469_, 1);
return v_val_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(lean_object* v___f_472_, lean_object* v_s_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(v___f_472_, v_s_473_, v_x_474_);
lean_dec_ref(v_s_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object* v_as_480_, size_t v_sz_481_, size_t v_i_482_, lean_object* v_b_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_484_ == 0)
{
return v_b_483_;
}
else
{
lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_565_; 
v_fst_485_ = lean_ctor_get(v_b_483_, 0);
v_snd_486_ = lean_ctor_get(v_b_483_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_b_483_);
if (v_isSharedCheck_565_ == 0)
{
v___x_488_ = v_b_483_;
v_isShared_489_ = v_isSharedCheck_565_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_snd_486_);
lean_inc(v_fst_485_);
lean_dec(v_b_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_565_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___y_491_; lean_object* v_a_500_; lean_object* v___y_502_; lean_object* v_i_503_; lean_object* v___y_509_; lean_object* v___y_519_; lean_object* v_i_520_; lean_object* v___x_535_; 
v_a_500_ = lean_array_uget_borrowed(v_as_480_, v_i_482_);
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_fst_485_, v_a_500_);
switch(lean_obj_tag(v___x_535_))
{
case 0:
{
lean_object* v_index_536_; lean_object* v_size_537_; lean_object* v___x_538_; 
v_index_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_index_536_);
lean_dec_ref_known(v___x_535_, 3);
v_size_537_ = lean_ctor_get(v_fst_485_, 0);
lean_inc(v_size_537_);
lean_inc(v_snd_486_);
lean_inc(v_a_500_);
v___x_538_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_485_, v_size_537_, v_index_536_, v_a_500_, v_snd_486_);
lean_dec(v_index_536_);
v___y_491_ = v___x_538_;
goto v___jp_490_;
}
case 1:
{
lean_object* v_index_539_; lean_object* v_size_540_; lean_object* v_keyArray_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_index_539_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_index_539_);
lean_dec_ref_known(v___x_535_, 1);
v_size_540_ = lean_ctor_get(v_fst_485_, 0);
v_keyArray_541_ = lean_ctor_get(v_fst_485_, 1);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_size_540_, v___x_542_);
v___x_544_ = lean_array_get_size(v_keyArray_541_);
v___x_545_ = lean_nat_dec_lt(v___x_543_, v___x_544_);
if (v___x_545_ == 0)
{
lean_dec(v___x_543_);
lean_dec(v_index_539_);
goto v___jp_525_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_546_ = lean_unsigned_to_nat(4u);
v___x_547_ = lean_nat_mul(v___x_543_, v___x_546_);
v___x_548_ = lean_unsigned_to_nat(3u);
v___x_549_ = lean_nat_mul(v___x_544_, v___x_548_);
v___x_550_ = lean_nat_dec_le(v___x_547_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v___x_547_);
if (v___x_550_ == 0)
{
lean_dec(v___x_543_);
lean_dec(v_index_539_);
goto v___jp_525_;
}
else
{
lean_object* v___x_551_; 
lean_inc(v_snd_486_);
lean_inc(v_a_500_);
v___x_551_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_485_, v___x_543_, v_index_539_, v_a_500_, v_snd_486_);
lean_dec(v_index_539_);
v___y_491_ = v___x_551_;
goto v___jp_490_;
}
}
}
default: 
{
lean_object* v_size_552_; lean_object* v_keyArray_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_size_552_ = lean_ctor_get(v_fst_485_, 0);
v_keyArray_553_ = lean_ctor_get(v_fst_485_, 1);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_size_552_, v___x_554_);
v___x_556_ = lean_array_get_size(v_keyArray_553_);
v___x_557_ = lean_nat_dec_lt(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v___x_555_);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_fst_485_);
lean_dec(v_fst_485_);
v___y_509_ = v___x_558_;
goto v___jp_508_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_nat_mul(v___x_555_, v___x_559_);
lean_dec(v___x_555_);
v___x_561_ = lean_unsigned_to_nat(3u);
v___x_562_ = lean_nat_mul(v___x_556_, v___x_561_);
v___x_563_ = lean_nat_dec_le(v___x_560_, v___x_562_);
lean_dec(v___x_562_);
lean_dec(v___x_560_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_fst_485_);
lean_dec(v_fst_485_);
v___y_509_ = v___x_564_;
goto v___jp_508_;
}
else
{
v___y_509_ = v_fst_485_;
goto v___jp_508_;
}
}
}
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_snd_486_, v___x_492_);
lean_dec(v_snd_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 1, v___x_493_);
lean_ctor_set(v___x_488_, 0, v___y_491_);
v___x_495_ = v___x_488_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___y_491_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
size_t v___x_496_; size_t v___x_497_; 
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_482_, v___x_496_);
v_i_482_ = v___x_497_;
v_b_483_ = v___x_495_;
goto _start;
}
}
v___jp_501_:
{
lean_object* v_size_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_size_504_ = lean_ctor_get(v___y_502_, 0);
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_size_504_, v___x_505_);
lean_inc(v_snd_486_);
lean_inc(v_a_500_);
v___x_507_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_502_, v___x_506_, v_i_503_, v_a_500_, v_snd_486_);
lean_dec(v_i_503_);
v___y_491_ = v___x_507_;
goto v___jp_490_;
}
v___jp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v___y_509_, v_a_500_);
switch(lean_obj_tag(v___x_510_))
{
case 0:
{
lean_object* v_index_511_; lean_object* v_size_512_; lean_object* v___x_513_; 
v_index_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_index_511_);
lean_dec_ref_known(v___x_510_, 3);
v_size_512_ = lean_ctor_get(v___y_509_, 0);
lean_inc(v_size_512_);
lean_inc(v_snd_486_);
lean_inc(v_a_500_);
v___x_513_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_509_, v_size_512_, v_index_511_, v_a_500_, v_snd_486_);
lean_dec(v_index_511_);
v___y_491_ = v___x_513_;
goto v___jp_490_;
}
case 1:
{
lean_object* v_index_514_; 
v_index_514_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_index_514_);
lean_dec_ref_known(v___x_510_, 1);
v___y_502_ = v___y_509_;
v_i_503_ = v_index_514_;
goto v___jp_501_;
}
default: 
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_509_, v___x_515_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_index_517_; 
v_index_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_index_517_);
lean_dec_ref_known(v___x_516_, 1);
v___y_502_ = v___y_509_;
v_i_503_ = v_index_517_;
goto v___jp_501_;
}
else
{
v___y_491_ = v___y_509_;
goto v___jp_490_;
}
}
}
}
v___jp_518_:
{
lean_object* v_size_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_size_521_ = lean_ctor_get(v___y_519_, 0);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_size_521_, v___x_522_);
lean_inc(v_snd_486_);
lean_inc(v_a_500_);
v___x_524_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_519_, v___x_523_, v_i_520_, v_a_500_, v_snd_486_);
lean_dec(v_i_520_);
v___y_491_ = v___x_524_;
goto v___jp_490_;
}
v___jp_525_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Grind_collectVar_spec__1___redArg(v_fst_485_);
lean_dec(v_fst_485_);
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v___x_526_, v_a_500_);
switch(lean_obj_tag(v___x_527_))
{
case 0:
{
lean_object* v_index_528_; lean_object* v_size_529_; lean_object* v___x_530_; 
v_index_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_index_528_);
lean_dec_ref_known(v___x_527_, 3);
v_size_529_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_size_529_);
lean_inc(v_snd_486_);
lean_inc(v_a_500_);
v___x_530_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_526_, v_size_529_, v_index_528_, v_a_500_, v_snd_486_);
lean_dec(v_index_528_);
v___y_491_ = v___x_530_;
goto v___jp_490_;
}
case 1:
{
lean_object* v_index_531_; 
v_index_531_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_index_531_);
lean_dec_ref_known(v___x_527_, 1);
v___y_519_ = v___x_526_;
v_i_520_ = v_index_531_;
goto v___jp_518_;
}
default: 
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_526_, v___x_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_index_534_; 
v_index_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_index_534_);
lean_dec_ref_known(v___x_533_, 1);
v___y_519_ = v___x_526_;
v_i_520_ = v_index_534_;
goto v___jp_518_;
}
else
{
v___y_491_ = v___x_526_;
goto v___jp_490_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__0___boxed(lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_){
_start:
{
size_t v_sz_boxed_570_; size_t v_i_boxed_571_; lean_object* v_res_572_; 
v_sz_boxed_570_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_571_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__0(v_as_566_, v_sz_boxed_570_, v_i_boxed_571_, v_b_569_);
lean_dec_ref(v_as_566_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__0(void){
_start:
{
lean_object* v_cellCount_573_; lean_object* v___x_574_; 
v_cellCount_573_ = lean_unsigned_to_nat(16u);
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__1(void){
_start:
{
lean_object* v_cellCount_575_; lean_object* v___x_576_; 
v_cellCount_575_ = lean_unsigned_to_nat(16u);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__2(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_old2new_580_; 
v___x_577_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__1, &l_Lean_Meta_Grind_mkVarRename___closed__1_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__1);
v___x_578_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__0, &l_Lean_Meta_Grind_mkVarRename___closed__0_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__0);
v___x_579_ = lean_unsigned_to_nat(0u);
v_old2new_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_old2new_580_, 0, v___x_579_);
lean_ctor_set(v_old2new_580_, 1, v___x_578_);
lean_ctor_set(v_old2new_580_, 2, v___x_577_);
return v_old2new_580_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v_old2new_582_; lean_object* v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v_old2new_582_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__2, &l_Lean_Meta_Grind_mkVarRename___closed__2_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__2);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_old2new_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object* v_new2old_584_){
_start:
{
lean_object* v___x_585_; size_t v_sz_586_; size_t v___x_587_; lean_object* v___x_588_; lean_object* v_fst_589_; 
v___x_585_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__3, &l_Lean_Meta_Grind_mkVarRename___closed__3_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__3);
v_sz_586_ = lean_array_size(v_new2old_584_);
v___x_587_ = ((size_t)0ULL);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__0(v_new2old_584_, v_sz_586_, v___x_587_, v___x_585_);
v_fst_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_fst_589_);
lean_dec_ref(v___x_588_);
return v_fst_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object* v_new2old_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_Grind_mkVarRename(v_new2old_590_);
lean_dec_ref(v_new2old_590_);
return v_res_591_;
}
}
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_QSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
