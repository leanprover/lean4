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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instAndThenVarCollector___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instAndThenVarCollector = (const lean_object*)&l_Lean_Meta_Grind_instAndThenVarCollector___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__0_value)} };
static const lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar = (const lean_object*)&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_mkVarRename___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_mkVarRename___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
v___x_6_ = lean_nat_dec_eq(v_key_4_, v_a_1_);
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
return v_x_13_;
}
else
{
lean_object* v_key_15_; lean_object* v_value_16_; lean_object* v_tail_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_40_; 
v_key_15_ = lean_ctor_get(v_x_14_, 0);
v_value_16_ = lean_ctor_get(v_x_14_, 1);
v_tail_17_ = lean_ctor_get(v_x_14_, 2);
v_isSharedCheck_40_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_40_ == 0)
{
v___x_19_ = v_x_14_;
v_isShared_20_ = v_isSharedCheck_40_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_tail_17_);
lean_inc(v_value_16_);
lean_inc(v_key_15_);
lean_dec(v_x_14_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_40_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v_fold_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_21_ = lean_array_get_size(v_x_13_);
v___x_22_ = lean_uint64_of_nat(v_key_15_);
v___x_23_ = 32ULL;
v___x_24_ = lean_uint64_shift_right(v___x_22_, v___x_23_);
v_fold_25_ = lean_uint64_xor(v___x_22_, v___x_24_);
v___x_26_ = 16ULL;
v___x_27_ = lean_uint64_shift_right(v_fold_25_, v___x_26_);
v___x_28_ = lean_uint64_xor(v_fold_25_, v___x_27_);
v___x_29_ = lean_uint64_to_usize(v___x_28_);
v___x_30_ = lean_usize_of_nat(v___x_21_);
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_sub(v___x_30_, v___x_31_);
v___x_33_ = lean_usize_land(v___x_29_, v___x_32_);
v___x_34_ = lean_array_uget_borrowed(v_x_13_, v___x_33_);
lean_inc(v___x_34_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 2, v___x_34_);
v___x_36_ = v___x_19_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_key_15_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_value_16_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v___x_34_);
v___x_36_ = v_reuseFailAlloc_39_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; 
v___x_37_ = lean_array_uset(v_x_13_, v___x_33_, v___x_36_);
v_x_13_ = v___x_37_;
v_x_14_ = v_tail_17_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_41_, lean_object* v_source_42_, lean_object* v_target_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_array_get_size(v_source_42_);
v___x_45_ = lean_nat_dec_lt(v_i_41_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec_ref(v_source_42_);
lean_dec(v_i_41_);
return v_target_43_;
}
else
{
lean_object* v_es_46_; lean_object* v___x_47_; lean_object* v_source_48_; lean_object* v_target_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_es_46_ = lean_array_fget(v_source_42_, v_i_41_);
v___x_47_ = lean_box(0);
v_source_48_ = lean_array_fset(v_source_42_, v_i_41_, v___x_47_);
v_target_49_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_43_, v_es_46_);
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_add(v_i_41_, v___x_50_);
lean_dec(v_i_41_);
v_i_41_ = v___x_51_;
v_source_42_ = v_source_48_;
v_target_43_ = v_target_49_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(lean_object* v_data_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_nbuckets_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_54_ = lean_array_get_size(v_data_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v_nbuckets_56_ = lean_nat_mul(v___x_54_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_box(0);
v___x_59_ = lean_mk_array(v_nbuckets_56_, v___x_58_);
v___x_60_ = lean_array_propagate_mark(v_data_53_, v___x_59_);
v___x_61_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v___x_57_, v_data_53_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(lean_object* v_m_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
lean_object* v_size_65_; lean_object* v_buckets_66_; lean_object* v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v_fold_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v_bkt_80_; uint8_t v___x_81_; 
v_size_65_ = lean_ctor_get(v_m_62_, 0);
v_buckets_66_ = lean_ctor_get(v_m_62_, 1);
v___x_67_ = lean_array_get_size(v_buckets_66_);
v___x_68_ = lean_uint64_of_nat(v_a_63_);
v___x_69_ = 32ULL;
v___x_70_ = lean_uint64_shift_right(v___x_68_, v___x_69_);
v_fold_71_ = lean_uint64_xor(v___x_68_, v___x_70_);
v___x_72_ = 16ULL;
v___x_73_ = lean_uint64_shift_right(v_fold_71_, v___x_72_);
v___x_74_ = lean_uint64_xor(v_fold_71_, v___x_73_);
v___x_75_ = lean_uint64_to_usize(v___x_74_);
v___x_76_ = lean_usize_of_nat(v___x_67_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_sub(v___x_76_, v___x_77_);
v___x_79_ = lean_usize_land(v___x_75_, v___x_78_);
v_bkt_80_ = lean_array_uget_borrowed(v_buckets_66_, v___x_79_);
v___x_81_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_63_, v_bkt_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_buckets_66_);
lean_inc(v_size_65_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_m_62_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; 
v_unused_103_ = lean_ctor_get(v_m_62_, 1);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_m_62_, 0);
lean_dec(v_unused_104_);
v___x_83_ = v_m_62_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_m_62_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_size_x27_86_; lean_object* v___x_87_; lean_object* v_buckets_x27_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_size_x27_86_ = lean_nat_add(v_size_65_, v___x_85_);
lean_dec(v_size_65_);
lean_inc(v_bkt_80_);
v___x_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_87_, 0, v_a_63_);
lean_ctor_set(v___x_87_, 1, v_b_64_);
lean_ctor_set(v___x_87_, 2, v_bkt_80_);
v_buckets_x27_88_ = lean_array_uset(v_buckets_66_, v___x_79_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(4u);
v___x_90_ = lean_nat_mul(v_size_x27_86_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = lean_nat_div(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_array_get_size(v_buckets_x27_88_);
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v_val_95_; lean_object* v___x_97_; 
v_val_95_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_88_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_val_95_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_97_ = v___x_83_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_val_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_100_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_buckets_x27_88_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_buckets_x27_88_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_dec(v_b_64_);
lean_dec(v_a_63_);
return v_m_62_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectVar(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_x_106_, v_x_105_, v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0(lean_object* v_00_u03b2_109_, lean_object* v_m_110_, lean_object* v_a_111_, lean_object* v_b_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_m_110_, v_a_111_, v_b_112_);
return v___x_113_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_object* v_00_u03b2_114_, lean_object* v_a_115_, lean_object* v_x_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_115_, v_x_116_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_115_ = stack[1].m_obj;
lean_object* v_x_116_ = stack[2].m_obj;
uint8_t v_res_118_;
v_res_118_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_box(0), v_a_115_, v_x_116_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_119_, lean_object* v_a_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(v_00_u03b2_119_, v_a_120_, v_x_121_);
lean_dec(v_x_121_);
lean_dec(v_a_120_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1(lean_object* v_00_u03b2_124_, lean_object* v_data_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_data_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_127_, lean_object* v_i_128_, lean_object* v_source_129_, lean_object* v_target_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v_i_128_, v_source_129_, v_target_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_132_, lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(lean_object* v_c_u2081_136_, lean_object* v_c_u2082_137_, lean_object* v_s_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_1(v_c_u2081_136_, v_s_138_);
v___x_141_ = lean_apply_2(v_c_u2082_137_, v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(lean_object* v_k_144_, lean_object* v_a_145_, lean_object* v_b_146_, lean_object* v_acc_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_apply_2(v_k_144_, v_a_145_, v_acc_147_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(lean_object* v_k_150_, lean_object* v_a_151_, lean_object* v_b_152_, lean_object* v_acc_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(v_k_150_, v_a_151_, v_b_152_, v_acc_153_);
lean_dec(v_b_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__1(lean_object* v___x_155_, lean_object* v___f_156_, lean_object* v_a_157_, lean_object* v_x_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_155_, v___f_156_, v_a_157_, v___y_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg(lean_object* v_m_180_, lean_object* v_k_181_, lean_object* v_s_182_){
_start:
{
lean_object* v___x_183_; lean_object* v_buckets_184_; lean_object* v___f_185_; lean_object* v___f_186_; size_t v_sz_187_; size_t v___x_188_; lean_object* v___x_189_; 
v___x_183_ = ((lean_object*)(l_Lean_Meta_Grind_collectMapVars___redArg___closed__9));
v_buckets_184_ = lean_ctor_get(v_m_180_, 1);
lean_inc_ref(v_buckets_184_);
lean_dec_ref(v_m_180_);
v___f_185_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_185_, 0, v_k_181_);
v___f_186_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__1), 5, 2);
lean_closure_set(v___f_186_, 0, v___x_183_);
lean_closure_set(v___f_186_, 1, v___f_185_);
v_sz_187_ = lean_array_size(v_buckets_184_);
v___x_188_ = ((size_t)0ULL);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_183_, v_buckets_184_, v___f_186_, v_sz_187_, v___x_188_, v_s_182_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars(lean_object* v_00_u03b1_190_, lean_object* v_Expr_191_, lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_m_194_, lean_object* v_k_195_, lean_object* v_s_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Grind_collectMapVars___redArg(v_m_194_, v_k_195_, v_s_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___boxed(lean_object* v_00_u03b1_198_, lean_object* v_Expr_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_m_202_, lean_object* v_k_203_, lean_object* v_s_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Meta_Grind_collectMapVars(v_00_u03b1_198_, v_Expr_199_, v_x_200_, v_x_201_, v_m_202_, v_k_203_, v_s_204_);
lean_dec_ref(v_x_201_);
lean_dec_ref(v_x_200_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
return v_x_206_;
}
else
{
lean_object* v_key_208_; lean_object* v_tail_209_; lean_object* v___x_210_; 
v_key_208_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_key_208_);
v_tail_209_ = lean_ctor_get(v_x_207_, 2);
lean_inc(v_tail_209_);
lean_dec_ref_known(v_x_207_, 3);
v___x_210_ = lean_array_push(v_x_206_, v_key_208_);
v_x_206_ = v___x_210_;
v_x_207_ = v_tail_209_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(lean_object* v_as_212_, size_t v_i_213_, size_t v_stop_214_, lean_object* v_b_215_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_eq(v_i_213_, v_stop_214_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; size_t v___x_219_; size_t v___x_220_; 
v___x_217_ = lean_array_uget_borrowed(v_as_212_, v_i_213_);
lean_inc(v___x_217_);
v___x_218_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(v_b_215_, v___x_217_);
v___x_219_ = ((size_t)1ULL);
v___x_220_ = lean_usize_add(v_i_213_, v___x_219_);
v_i_213_ = v___x_220_;
v_b_215_ = v___x_218_;
goto _start;
}
else
{
return v_b_215_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_212_ = stack[0].m_obj;
size_t v_i_213_ = stack[1].m_num;
size_t v_stop_214_ = stack[2].m_num;
lean_object* v_b_215_ = stack[3].m_obj;
lean_object* v_res_222_;
v_res_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_as_212_, v_i_213_, v_stop_214_, v_b_215_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2___boxed(lean_object* v_as_223_, lean_object* v_i_224_, lean_object* v_stop_225_, lean_object* v_b_226_){
_start:
{
size_t v_i_boxed_227_; size_t v_stop_boxed_228_; lean_object* v_res_229_; 
v_i_boxed_227_ = lean_unbox_usize(v_i_224_);
lean_dec(v_i_224_);
v_stop_boxed_228_ = lean_unbox_usize(v_stop_225_);
lean_dec(v_stop_225_);
v_res_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_as_223_, v_i_boxed_227_, v_stop_boxed_228_, v_b_226_);
lean_dec_ref(v_as_223_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(lean_object* v_hi_230_, lean_object* v_pivot_231_, lean_object* v_as_232_, lean_object* v_i_233_, lean_object* v_k_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = lean_nat_dec_lt(v_k_234_, v_hi_230_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_k_234_);
v___x_236_ = lean_array_fswap(v_as_232_, v_i_233_, v_hi_230_);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v_i_233_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_array_fget_borrowed(v_as_232_, v_k_234_);
v___x_239_ = lean_nat_dec_lt(v___x_238_, v_pivot_231_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_k_234_, v___x_240_);
lean_dec(v_k_234_);
v_k_234_ = v___x_241_;
goto _start;
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_array_fswap(v_as_232_, v_i_233_, v_k_234_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_i_233_, v___x_244_);
lean_dec(v_i_233_);
v___x_246_ = lean_nat_add(v_k_234_, v___x_244_);
lean_dec(v_k_234_);
v_as_232_ = v___x_243_;
v_i_233_ = v___x_245_;
v_k_234_ = v___x_246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_hi_248_, lean_object* v_pivot_249_, lean_object* v_as_250_, lean_object* v_i_251_, lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_248_, v_pivot_249_, v_as_250_, v_i_251_, v_k_252_);
lean_dec(v_pivot_249_);
lean_dec(v_hi_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(lean_object* v_n_254_, lean_object* v_as_255_, lean_object* v_lo_256_, lean_object* v_hi_257_){
_start:
{
lean_object* v___y_259_; uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_lt(v_lo_256_, v_hi_257_);
if (v___x_269_ == 0)
{
lean_dec(v_lo_256_);
return v_as_255_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_mid_272_; lean_object* v___y_274_; lean_object* v___y_280_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_270_ = lean_nat_add(v_lo_256_, v_hi_257_);
v___x_271_ = lean_unsigned_to_nat(1u);
v_mid_272_ = lean_nat_shiftr(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
v___x_285_ = lean_array_fget_borrowed(v_as_255_, v_mid_272_);
v___x_286_ = lean_array_fget_borrowed(v_as_255_, v_lo_256_);
v___x_287_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
v___y_280_ = v_as_255_;
goto v___jp_279_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_array_fswap(v_as_255_, v_lo_256_, v_mid_272_);
v___y_280_ = v___x_288_;
goto v___jp_279_;
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = lean_array_fget_borrowed(v___y_274_, v_mid_272_);
v___x_276_ = lean_array_fget_borrowed(v___y_274_, v_hi_257_);
v___x_277_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_dec(v_mid_272_);
v___y_259_ = v___y_274_;
goto v___jp_258_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_array_fswap(v___y_274_, v_mid_272_, v_hi_257_);
lean_dec(v_mid_272_);
v___y_259_ = v___x_278_;
goto v___jp_258_;
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_array_fget_borrowed(v___y_280_, v_hi_257_);
v___x_282_ = lean_array_fget_borrowed(v___y_280_, v_lo_256_);
v___x_283_ = lean_nat_dec_lt(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
v___y_274_ = v___y_280_;
goto v___jp_273_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_fswap(v___y_280_, v_lo_256_, v_hi_257_);
v___y_274_ = v___x_284_;
goto v___jp_273_;
}
}
}
v___jp_258_:
{
lean_object* v_pivot_260_; lean_object* v___x_261_; lean_object* v_fst_262_; lean_object* v_snd_263_; uint8_t v___x_264_; 
v_pivot_260_ = lean_array_fget(v___y_259_, v_hi_257_);
lean_inc_n(v_lo_256_, 2);
v___x_261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_257_, v_pivot_260_, v___y_259_, v_lo_256_, v_lo_256_);
lean_dec(v_pivot_260_);
v_fst_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_fst_262_);
v_snd_263_ = lean_ctor_get(v___x_261_, 1);
lean_inc(v_snd_263_);
lean_dec_ref(v___x_261_);
v___x_264_ = lean_nat_dec_le(v_hi_257_, v_fst_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_254_, v_snd_263_, v_lo_256_, v_fst_262_);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_fst_262_, v___x_266_);
lean_dec(v_fst_262_);
v_as_255_ = v___x_265_;
v_lo_256_ = v___x_267_;
goto _start;
}
else
{
lean_dec(v_fst_262_);
lean_dec(v_lo_256_);
return v_snd_263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(lean_object* v_n_289_, lean_object* v_as_290_, lean_object* v_lo_291_, lean_object* v_hi_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_289_, v_as_290_, v_lo_291_, v_hi_292_);
lean_dec(v_hi_292_);
lean_dec(v_n_289_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object* v_s_294_){
_start:
{
lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; lean_object* v___y_304_; lean_object* v_size_311_; lean_object* v_buckets_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_size_311_ = lean_ctor_get(v_s_294_, 0);
v_buckets_312_ = lean_ctor_get(v_s_294_, 1);
v___x_313_ = lean_mk_empty_array_with_capacity(v_size_311_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_array_get_size(v_buckets_312_);
v___x_316_ = lean_nat_dec_lt(v___x_314_, v___x_315_);
if (v___x_316_ == 0)
{
v___y_304_ = v___x_313_;
goto v___jp_303_;
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_of_nat(v___x_315_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_312_, v___x_317_, v___x_318_, v___x_313_);
v___y_304_ = v___x_319_;
goto v___jp_303_;
}
v___jp_295_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_nat_dec_le(v___y_299_, v___y_297_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec(v___y_297_);
lean_inc(v___y_299_);
v___x_301_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_298_, v___y_296_, v___y_299_, v___y_299_);
lean_dec(v___y_299_);
lean_dec(v___y_298_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_298_, v___y_296_, v___y_299_, v___y_297_);
lean_dec(v___y_297_);
lean_dec(v___y_298_);
return v___x_302_;
}
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_array_get_size(v___y_304_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_sub(v___x_305_, v___x_308_);
v___x_310_ = lean_nat_dec_le(v___x_306_, v___x_309_);
if (v___x_310_ == 0)
{
lean_inc(v___x_309_);
v___y_296_ = v___y_304_;
v___y_297_ = v___x_309_;
v___y_298_ = v___x_305_;
v___y_299_ = v___x_309_;
goto v___jp_295_;
}
else
{
v___y_296_ = v___y_304_;
v___y_297_ = v___x_309_;
v___y_298_ = v___x_305_;
v___y_299_ = v___x_306_;
goto v___jp_295_;
}
}
else
{
return v___y_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object* v_s_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Meta_Grind_FoundVars_toArray(v_s_320_);
lean_dec_ref(v_s_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object* v_n_322_, lean_object* v_as_323_, lean_object* v_lo_324_, lean_object* v_hi_325_, lean_object* v_w_326_, lean_object* v_hlo_327_, lean_object* v_hhi_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_322_, v_as_323_, v_lo_324_, v_hi_325_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object* v_n_330_, lean_object* v_as_331_, lean_object* v_lo_332_, lean_object* v_hi_333_, lean_object* v_w_334_, lean_object* v_hlo_335_, lean_object* v_hhi_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(v_n_330_, v_as_331_, v_lo_332_, v_hi_333_, v_w_334_, v_hlo_335_, v_hhi_336_);
lean_dec(v_hi_333_);
lean_dec(v_n_330_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(lean_object* v_n_338_, lean_object* v_lo_339_, lean_object* v_hi_340_, lean_object* v_hhi_341_, lean_object* v_pivot_342_, lean_object* v_as_343_, lean_object* v_i_344_, lean_object* v_k_345_, lean_object* v_ilo_346_, lean_object* v_ik_347_, lean_object* v_w_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_340_, v_pivot_342_, v_as_343_, v_i_344_, v_k_345_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___boxed(lean_object* v_n_350_, lean_object* v_lo_351_, lean_object* v_hi_352_, lean_object* v_hhi_353_, lean_object* v_pivot_354_, lean_object* v_as_355_, lean_object* v_i_356_, lean_object* v_k_357_, lean_object* v_ilo_358_, lean_object* v_ik_359_, lean_object* v_w_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(v_n_350_, v_lo_351_, v_hi_352_, v_hhi_353_, v_pivot_354_, v_as_355_, v_i_356_, v_k_357_, v_ilo_358_, v_ik_359_, v_w_360_);
lean_dec(v_pivot_354_);
lean_dec(v_hi_352_);
lean_dec(v_lo_351_);
lean_dec(v_n_350_);
return v_res_361_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_362_; lean_object* v___f_363_; 
v___x_362_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_363_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_363_, 0, v___x_362_);
return v___f_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(lean_object* v___f_364_, lean_object* v_s_365_, lean_object* v_x_366_){
_start:
{
lean_object* v___f_367_; lean_object* v___x_368_; 
v___f_367_ = lean_obj_once(&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0, &l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0);
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_367_, v___f_364_, v_s_365_, v_x_366_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v___x_369_; 
v___x_369_ = lean_unsigned_to_nat(0u);
return v___x_369_;
}
else
{
lean_object* v_val_370_; 
v_val_370_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v___x_368_, 1);
return v_val_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(lean_object* v___f_371_, lean_object* v_s_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(v___f_371_, v_s_372_, v_x_373_);
lean_dec_ref(v_s_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(lean_object* v_a_379_, lean_object* v_b_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_dec(v_b_380_);
lean_dec(v_a_379_);
return v_x_381_;
}
else
{
lean_object* v_key_382_; lean_object* v_value_383_; lean_object* v_tail_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_396_; 
v_key_382_ = lean_ctor_get(v_x_381_, 0);
v_value_383_ = lean_ctor_get(v_x_381_, 1);
v_tail_384_ = lean_ctor_get(v_x_381_, 2);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_381_);
if (v_isSharedCheck_396_ == 0)
{
v___x_386_ = v_x_381_;
v_isShared_387_ = v_isSharedCheck_396_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_tail_384_);
lean_inc(v_value_383_);
lean_inc(v_key_382_);
lean_dec(v_x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_396_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint8_t v___x_388_; 
v___x_388_ = lean_nat_dec_eq(v_key_382_, v_a_379_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_379_, v_b_380_, v_tail_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_389_);
v___x_391_ = v___x_386_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_key_382_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_value_383_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v___x_389_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
else
{
lean_object* v___x_394_; 
lean_dec(v_value_383_);
lean_dec(v_key_382_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_b_380_);
lean_ctor_set(v___x_386_, 0, v_a_379_);
v___x_394_ = v___x_386_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_b_380_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_tail_384_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(lean_object* v_m_397_, lean_object* v_a_398_, lean_object* v_b_399_){
_start:
{
lean_object* v_size_400_; lean_object* v_buckets_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_444_; 
v_size_400_ = lean_ctor_get(v_m_397_, 0);
v_buckets_401_ = lean_ctor_get(v_m_397_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_m_397_);
if (v_isSharedCheck_444_ == 0)
{
v___x_403_ = v_m_397_;
v_isShared_404_ = v_isSharedCheck_444_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_buckets_401_);
lean_inc(v_size_400_);
lean_dec(v_m_397_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_444_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v_fold_409_; uint64_t v___x_410_; uint64_t v___x_411_; uint64_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v_bkt_418_; uint8_t v___x_419_; 
v___x_405_ = lean_array_get_size(v_buckets_401_);
v___x_406_ = lean_uint64_of_nat(v_a_398_);
v___x_407_ = 32ULL;
v___x_408_ = lean_uint64_shift_right(v___x_406_, v___x_407_);
v_fold_409_ = lean_uint64_xor(v___x_406_, v___x_408_);
v___x_410_ = 16ULL;
v___x_411_ = lean_uint64_shift_right(v_fold_409_, v___x_410_);
v___x_412_ = lean_uint64_xor(v_fold_409_, v___x_411_);
v___x_413_ = lean_uint64_to_usize(v___x_412_);
v___x_414_ = lean_usize_of_nat(v___x_405_);
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_sub(v___x_414_, v___x_415_);
v___x_417_ = lean_usize_land(v___x_413_, v___x_416_);
v_bkt_418_ = lean_array_uget_borrowed(v_buckets_401_, v___x_417_);
v___x_419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_398_, v_bkt_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v_size_x27_421_; lean_object* v___x_422_; lean_object* v_buckets_x27_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v_size_x27_421_ = lean_nat_add(v_size_400_, v___x_420_);
lean_dec(v_size_400_);
lean_inc(v_bkt_418_);
v___x_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_422_, 0, v_a_398_);
lean_ctor_set(v___x_422_, 1, v_b_399_);
lean_ctor_set(v___x_422_, 2, v_bkt_418_);
v_buckets_x27_423_ = lean_array_uset(v_buckets_401_, v___x_417_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(4u);
v___x_425_ = lean_nat_mul(v_size_x27_421_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = lean_nat_div(v___x_425_, v___x_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_array_get_size(v_buckets_x27_423_);
v___x_429_ = lean_nat_dec_le(v___x_427_, v___x_428_);
lean_dec(v___x_427_);
if (v___x_429_ == 0)
{
lean_object* v_val_430_; lean_object* v___x_432_; 
v_val_430_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_423_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_val_430_);
lean_ctor_set(v___x_403_, 0, v_size_x27_421_);
v___x_432_ = v___x_403_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_size_x27_421_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_val_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v___x_435_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v_buckets_x27_423_);
lean_ctor_set(v___x_403_, 0, v_size_x27_421_);
v___x_435_ = v___x_403_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_size_x27_421_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_buckets_x27_423_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v___x_437_; lean_object* v_buckets_x27_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
lean_inc(v_bkt_418_);
v___x_437_ = lean_box(0);
v_buckets_x27_438_ = lean_array_uset(v_buckets_401_, v___x_417_, v___x_437_);
v___x_439_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_398_, v_b_399_, v_bkt_418_);
v___x_440_ = lean_array_uset(v_buckets_x27_438_, v___x_417_, v___x_439_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v___x_440_);
v___x_442_ = v___x_403_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_size_400_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(lean_object* v_as_445_, size_t v_sz_446_, size_t v_i_447_, lean_object* v_b_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_lt(v_i_447_, v_sz_446_);
if (v___x_449_ == 0)
{
return v_b_448_;
}
else
{
lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_465_; 
v_fst_450_ = lean_ctor_get(v_b_448_, 0);
v_snd_451_ = lean_ctor_get(v_b_448_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_b_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_453_ = v_b_448_;
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_snd_451_);
lean_inc(v_fst_450_);
lean_dec(v_b_448_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_a_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v_a_455_ = lean_array_uget_borrowed(v_as_445_, v_i_447_);
lean_inc(v_snd_451_);
lean_inc(v_a_455_);
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_fst_450_, v_a_455_, v_snd_451_);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_snd_451_, v___x_457_);
lean_dec(v_snd_451_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_458_);
lean_ctor_set(v___x_453_, 0, v___x_456_);
v___x_460_ = v___x_453_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
size_t v___x_461_; size_t v___x_462_; 
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_447_, v___x_461_);
v_i_447_ = v___x_462_;
v_b_448_ = v___x_460_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_445_ = stack[0].m_obj;
size_t v_sz_446_ = stack[1].m_num;
size_t v_i_447_ = stack[2].m_num;
lean_object* v_b_448_ = stack[3].m_obj;
lean_object* v_res_466_;
v_res_466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_as_445_, v_sz_446_, v_i_447_, v_b_448_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1___boxed(lean_object* v_as_467_, lean_object* v_sz_468_, lean_object* v_i_469_, lean_object* v_b_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_468_);
lean_dec(v_sz_468_);
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_as_467_, v_sz_boxed_471_, v_i_boxed_472_, v_b_470_);
lean_dec_ref(v_as_467_);
return v_res_473_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__0(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_unsigned_to_nat(16u);
v___x_476_ = lean_mk_array(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_old2new_479_; 
v___x_477_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__0, &l_Lean_Meta_Grind_mkVarRename___closed__0_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__0);
v___x_478_ = lean_unsigned_to_nat(0u);
v_old2new_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_old2new_479_, 0, v___x_478_);
lean_ctor_set(v_old2new_479_, 1, v___x_477_);
return v_old2new_479_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__2(void){
_start:
{
lean_object* v___x_480_; lean_object* v_old2new_481_; lean_object* v___x_482_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v_old2new_481_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__1, &l_Lean_Meta_Grind_mkVarRename___closed__1_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__1);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_old2new_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object* v_new2old_483_){
_start:
{
lean_object* v___x_484_; size_t v_sz_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v_fst_488_; 
v___x_484_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__2, &l_Lean_Meta_Grind_mkVarRename___closed__2_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__2);
v_sz_485_ = lean_array_size(v_new2old_483_);
v___x_486_ = ((size_t)0ULL);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_new2old_483_, v_sz_485_, v___x_486_, v___x_484_);
v_fst_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_fst_488_);
lean_dec_ref(v___x_487_);
return v_fst_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object* v_new2old_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Grind_mkVarRename(v_new2old_489_);
lean_dec_ref(v_new2old_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object* v_00_u03b2_491_, lean_object* v_m_492_, lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_m_492_, v_a_493_, v_b_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0(lean_object* v_00_u03b2_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v_x_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_497_, v_b_498_, v_x_499_);
return v___x_500_;
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
