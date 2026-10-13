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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
return v_x_12_;
}
else
{
lean_object* v_key_14_; lean_object* v_value_15_; lean_object* v_tail_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_39_; 
v_key_14_ = lean_ctor_get(v_x_13_, 0);
v_value_15_ = lean_ctor_get(v_x_13_, 1);
v_tail_16_ = lean_ctor_get(v_x_13_, 2);
v_isSharedCheck_39_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_39_ == 0)
{
v___x_18_ = v_x_13_;
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_tail_16_);
lean_inc(v_value_15_);
lean_inc(v_key_14_);
lean_dec(v_x_13_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v_fold_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_20_ = lean_array_get_size(v_x_12_);
v___x_21_ = lean_uint64_of_nat(v_key_14_);
v___x_22_ = 32ULL;
v___x_23_ = lean_uint64_shift_right(v___x_21_, v___x_22_);
v_fold_24_ = lean_uint64_xor(v___x_21_, v___x_23_);
v___x_25_ = 16ULL;
v___x_26_ = lean_uint64_shift_right(v_fold_24_, v___x_25_);
v___x_27_ = lean_uint64_xor(v_fold_24_, v___x_26_);
v___x_28_ = lean_uint64_to_usize(v___x_27_);
v___x_29_ = lean_usize_of_nat(v___x_20_);
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_sub(v___x_29_, v___x_30_);
v___x_32_ = lean_usize_land(v___x_28_, v___x_31_);
v___x_33_ = lean_array_uget_borrowed(v_x_12_, v___x_32_);
lean_inc(v___x_33_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v___x_33_);
v___x_35_ = v___x_18_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_key_14_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_value_15_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v___x_33_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_array_uset(v_x_12_, v___x_32_, v___x_35_);
v_x_12_ = v___x_36_;
v_x_13_ = v_tail_16_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(lean_object* v_i_40_, lean_object* v_source_41_, lean_object* v_target_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_array_get_size(v_source_41_);
v___x_44_ = lean_nat_dec_lt(v_i_40_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_source_41_);
lean_dec(v_i_40_);
return v_target_42_;
}
else
{
lean_object* v_es_45_; lean_object* v___x_46_; lean_object* v_source_47_; lean_object* v_target_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_es_45_ = lean_array_fget(v_source_41_, v_i_40_);
v___x_46_ = lean_box(0);
v_source_47_ = lean_array_fset(v_source_41_, v_i_40_, v___x_46_);
v_target_48_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_42_, v_es_45_);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_i_40_, v___x_49_);
lean_dec(v_i_40_);
v_i_40_ = v___x_50_;
v_source_41_ = v_source_47_;
v_target_42_ = v_target_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(lean_object* v_data_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_nbuckets_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_53_ = lean_array_get_size(v_data_52_);
v___x_54_ = lean_unsigned_to_nat(2u);
v_nbuckets_55_ = lean_nat_mul(v___x_53_, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_box(0);
v___x_58_ = lean_mk_array(v_nbuckets_55_, v___x_57_);
v___x_59_ = lean_array_propagate_mark(v_data_52_, v___x_58_);
v___x_60_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v___x_56_, v_data_52_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(lean_object* v_m_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v_size_64_; lean_object* v_buckets_65_; lean_object* v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_bkt_79_; uint8_t v___x_80_; 
v_size_64_ = lean_ctor_get(v_m_61_, 0);
v_buckets_65_ = lean_ctor_get(v_m_61_, 1);
v___x_66_ = lean_array_get_size(v_buckets_65_);
v___x_67_ = lean_uint64_of_nat(v_a_62_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_66_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v_bkt_79_ = lean_array_uget_borrowed(v_buckets_65_, v___x_78_);
v___x_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_62_, v_bkt_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
lean_inc_ref(v_buckets_65_);
lean_inc(v_size_64_);
v_isSharedCheck_101_ = !lean_is_exclusive(v_m_61_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_102_ = lean_ctor_get(v_m_61_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_m_61_, 0);
lean_dec(v_unused_103_);
v___x_82_ = v_m_61_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_m_61_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v_size_x27_85_; lean_object* v___x_86_; lean_object* v_buckets_x27_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v_size_x27_85_ = lean_nat_add(v_size_64_, v___x_84_);
lean_dec(v_size_64_);
lean_inc(v_bkt_79_);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v_a_62_);
lean_ctor_set(v___x_86_, 1, v_b_63_);
lean_ctor_set(v___x_86_, 2, v_bkt_79_);
v_buckets_x27_87_ = lean_array_uset(v_buckets_65_, v___x_78_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(4u);
v___x_89_ = lean_nat_mul(v_size_x27_85_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = lean_nat_div(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_array_get_size(v_buckets_x27_87_);
v___x_93_ = lean_nat_dec_le(v___x_91_, v___x_92_);
lean_dec(v___x_91_);
if (v___x_93_ == 0)
{
lean_object* v_val_94_; lean_object* v___x_96_; 
v_val_94_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_87_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_val_94_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_96_ = v___x_82_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_val_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_99_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_buckets_x27_87_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_99_ = v___x_82_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_buckets_x27_87_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
return v_m_61_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectVar(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_x_105_, v_x_104_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0(lean_object* v_00_u03b2_108_, lean_object* v_m_109_, lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_m_109_, v_a_110_, v_b_111_);
return v___x_112_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_object* v_00_u03b2_113_, lean_object* v_a_114_, lean_object* v_x_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_114_, v_x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_117_, lean_object* v_a_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(v_00_u03b2_117_, v_a_118_, v_x_119_);
lean_dec(v_x_119_);
lean_dec(v_a_118_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1(lean_object* v_00_u03b2_122_, lean_object* v_data_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_data_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_125_, lean_object* v_i_126_, lean_object* v_source_127_, lean_object* v_target_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v_i_126_, v_source_127_, v_target_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_131_, v_x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(lean_object* v_c_u2081_134_, lean_object* v_c_u2082_135_, lean_object* v_s_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
v___x_138_ = lean_apply_1(v_c_u2081_134_, v_s_136_);
v___x_139_ = lean_apply_2(v_c_u2082_135_, v___x_137_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(lean_object* v_k_142_, lean_object* v_a_143_, lean_object* v_b_144_, lean_object* v_acc_145_){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_apply_2(v_k_142_, v_a_143_, v_acc_145_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(lean_object* v_k_148_, lean_object* v_a_149_, lean_object* v_b_150_, lean_object* v_acc_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(v_k_148_, v_a_149_, v_b_150_, v_acc_151_);
lean_dec(v_b_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__1(lean_object* v___x_153_, lean_object* v___f_154_, lean_object* v_a_155_, lean_object* v_x_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_153_, v___f_154_, v_a_155_, v___y_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg(lean_object* v_m_178_, lean_object* v_k_179_, lean_object* v_s_180_){
_start:
{
lean_object* v___x_181_; lean_object* v_buckets_182_; lean_object* v___f_183_; lean_object* v___f_184_; size_t v_sz_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_181_ = ((lean_object*)(l_Lean_Meta_Grind_collectMapVars___redArg___closed__9));
v_buckets_182_ = lean_ctor_get(v_m_178_, 1);
lean_inc_ref(v_buckets_182_);
lean_dec_ref(v_m_178_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_183_, 0, v_k_179_);
v___f_184_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__1), 5, 2);
lean_closure_set(v___f_184_, 0, v___x_181_);
lean_closure_set(v___f_184_, 1, v___f_183_);
v_sz_185_ = lean_array_size(v_buckets_182_);
v___x_186_ = ((size_t)0ULL);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_181_, v_buckets_182_, v___f_184_, v_sz_185_, v___x_186_, v_s_180_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars(lean_object* v_00_u03b1_188_, lean_object* v_Expr_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_m_192_, lean_object* v_k_193_, lean_object* v_s_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_collectMapVars___redArg(v_m_192_, v_k_193_, v_s_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___boxed(lean_object* v_00_u03b1_196_, lean_object* v_Expr_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_m_200_, lean_object* v_k_201_, lean_object* v_s_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Meta_Grind_collectMapVars(v_00_u03b1_196_, v_Expr_197_, v_x_198_, v_x_199_, v_m_200_, v_k_201_, v_s_202_);
lean_dec_ref(v_x_199_);
lean_dec_ref(v_x_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
return v_x_204_;
}
else
{
lean_object* v_key_206_; lean_object* v_tail_207_; lean_object* v___x_208_; 
v_key_206_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_key_206_);
v_tail_207_ = lean_ctor_get(v_x_205_, 2);
lean_inc(v_tail_207_);
lean_dec_ref_known(v_x_205_, 3);
v___x_208_ = lean_array_push(v_x_204_, v_key_206_);
v_x_204_ = v___x_208_;
v_x_205_ = v_tail_207_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(lean_object* v_as_210_, size_t v_i_211_, size_t v_stop_212_, lean_object* v_b_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = lean_usize_dec_eq(v_i_211_, v_stop_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; size_t v___x_217_; size_t v___x_218_; 
v___x_215_ = lean_array_uget_borrowed(v_as_210_, v_i_211_);
lean_inc(v___x_215_);
v___x_216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(v_b_213_, v___x_215_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_add(v_i_211_, v___x_217_);
v_i_211_ = v___x_218_;
v_b_213_ = v___x_216_;
goto _start;
}
else
{
return v_b_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2___boxed(lean_object* v_as_220_, lean_object* v_i_221_, lean_object* v_stop_222_, lean_object* v_b_223_){
_start:
{
size_t v_i_boxed_224_; size_t v_stop_boxed_225_; lean_object* v_res_226_; 
v_i_boxed_224_ = lean_unbox_usize(v_i_221_);
lean_dec(v_i_221_);
v_stop_boxed_225_ = lean_unbox_usize(v_stop_222_);
lean_dec(v_stop_222_);
v_res_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_as_220_, v_i_boxed_224_, v_stop_boxed_225_, v_b_223_);
lean_dec_ref(v_as_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(lean_object* v_hi_227_, lean_object* v_pivot_228_, lean_object* v_as_229_, lean_object* v_i_230_, lean_object* v_k_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_nat_dec_lt(v_k_231_, v_hi_227_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_k_231_);
v___x_233_ = lean_array_fswap(v_as_229_, v_i_230_, v_hi_227_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v_i_230_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = lean_array_fget_borrowed(v_as_229_, v_k_231_);
v___x_236_ = lean_nat_dec_lt(v___x_235_, v_pivot_228_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_k_231_, v___x_237_);
lean_dec(v_k_231_);
v_k_231_ = v___x_238_;
goto _start;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = lean_array_fswap(v_as_229_, v_i_230_, v_k_231_);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_i_230_, v___x_241_);
lean_dec(v_i_230_);
v___x_243_ = lean_nat_add(v_k_231_, v___x_241_);
lean_dec(v_k_231_);
v_as_229_ = v___x_240_;
v_i_230_ = v___x_242_;
v_k_231_ = v___x_243_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_hi_245_, lean_object* v_pivot_246_, lean_object* v_as_247_, lean_object* v_i_248_, lean_object* v_k_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_245_, v_pivot_246_, v_as_247_, v_i_248_, v_k_249_);
lean_dec(v_pivot_246_);
lean_dec(v_hi_245_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(lean_object* v_n_251_, lean_object* v_as_252_, lean_object* v_lo_253_, lean_object* v_hi_254_){
_start:
{
lean_object* v___y_256_; uint8_t v___x_266_; 
v___x_266_ = lean_nat_dec_lt(v_lo_253_, v_hi_254_);
if (v___x_266_ == 0)
{
lean_dec(v_lo_253_);
return v_as_252_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_mid_269_; lean_object* v___y_271_; lean_object* v___y_277_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_267_ = lean_nat_add(v_lo_253_, v_hi_254_);
v___x_268_ = lean_unsigned_to_nat(1u);
v_mid_269_ = lean_nat_shiftr(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
v___x_282_ = lean_array_fget_borrowed(v_as_252_, v_mid_269_);
v___x_283_ = lean_array_fget_borrowed(v_as_252_, v_lo_253_);
v___x_284_ = lean_nat_dec_lt(v___x_282_, v___x_283_);
if (v___x_284_ == 0)
{
v___y_277_ = v_as_252_;
goto v___jp_276_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_array_fswap(v_as_252_, v_lo_253_, v_mid_269_);
v___y_277_ = v___x_285_;
goto v___jp_276_;
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_272_ = lean_array_fget_borrowed(v___y_271_, v_mid_269_);
v___x_273_ = lean_array_fget_borrowed(v___y_271_, v_hi_254_);
v___x_274_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec(v_mid_269_);
v___y_256_ = v___y_271_;
goto v___jp_255_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_array_fswap(v___y_271_, v_mid_269_, v_hi_254_);
lean_dec(v_mid_269_);
v___y_256_ = v___x_275_;
goto v___jp_255_;
}
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = lean_array_fget_borrowed(v___y_277_, v_hi_254_);
v___x_279_ = lean_array_fget_borrowed(v___y_277_, v_lo_253_);
v___x_280_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
v___y_271_ = v___y_277_;
goto v___jp_270_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_array_fswap(v___y_277_, v_lo_253_, v_hi_254_);
v___y_271_ = v___x_281_;
goto v___jp_270_;
}
}
}
v___jp_255_:
{
lean_object* v_pivot_257_; lean_object* v___x_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; uint8_t v___x_261_; 
v_pivot_257_ = lean_array_fget(v___y_256_, v_hi_254_);
lean_inc_n(v_lo_253_, 2);
v___x_258_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_254_, v_pivot_257_, v___y_256_, v_lo_253_, v_lo_253_);
lean_dec(v_pivot_257_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_fst_259_);
v_snd_260_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_snd_260_);
lean_dec_ref(v___x_258_);
v___x_261_ = lean_nat_dec_le(v_hi_254_, v_fst_259_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_251_, v_snd_260_, v_lo_253_, v_fst_259_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_fst_259_, v___x_263_);
lean_dec(v_fst_259_);
v_as_252_ = v___x_262_;
v_lo_253_ = v___x_264_;
goto _start;
}
else
{
lean_dec(v_fst_259_);
lean_dec(v_lo_253_);
return v_snd_260_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(lean_object* v_n_286_, lean_object* v_as_287_, lean_object* v_lo_288_, lean_object* v_hi_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_286_, v_as_287_, v_lo_288_, v_hi_289_);
lean_dec(v_hi_289_);
lean_dec(v_n_286_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object* v_s_291_){
_start:
{
lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_301_; lean_object* v_size_308_; lean_object* v_buckets_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_size_308_ = lean_ctor_get(v_s_291_, 0);
v_buckets_309_ = lean_ctor_get(v_s_291_, 1);
v___x_310_ = lean_mk_empty_array_with_capacity(v_size_308_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_array_get_size(v_buckets_309_);
v___x_313_ = lean_nat_dec_lt(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_301_ = v___x_310_;
goto v___jp_300_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_312_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_309_, v___x_314_, v___x_315_, v___x_310_);
v___y_301_ = v___x_316_;
goto v___jp_300_;
}
v___jp_292_:
{
uint8_t v___x_297_; 
v___x_297_ = lean_nat_dec_le(v___y_296_, v___y_294_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec(v___y_294_);
lean_inc(v___y_296_);
v___x_298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_295_, v___y_293_, v___y_296_, v___y_296_);
lean_dec(v___y_296_);
lean_dec(v___y_295_);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_295_, v___y_293_, v___y_296_, v___y_294_);
lean_dec(v___y_294_);
lean_dec(v___y_295_);
return v___x_299_;
}
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_array_get_size(v___y_301_);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_sub(v___x_302_, v___x_305_);
v___x_307_ = lean_nat_dec_le(v___x_303_, v___x_306_);
if (v___x_307_ == 0)
{
lean_inc(v___x_306_);
v___y_293_ = v___y_301_;
v___y_294_ = v___x_306_;
v___y_295_ = v___x_302_;
v___y_296_ = v___x_306_;
goto v___jp_292_;
}
else
{
v___y_293_ = v___y_301_;
v___y_294_ = v___x_306_;
v___y_295_ = v___x_302_;
v___y_296_ = v___x_303_;
goto v___jp_292_;
}
}
else
{
return v___y_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object* v_s_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Meta_Grind_FoundVars_toArray(v_s_317_);
lean_dec_ref(v_s_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object* v_n_319_, lean_object* v_as_320_, lean_object* v_lo_321_, lean_object* v_hi_322_, lean_object* v_w_323_, lean_object* v_hlo_324_, lean_object* v_hhi_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_319_, v_as_320_, v_lo_321_, v_hi_322_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object* v_n_327_, lean_object* v_as_328_, lean_object* v_lo_329_, lean_object* v_hi_330_, lean_object* v_w_331_, lean_object* v_hlo_332_, lean_object* v_hhi_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(v_n_327_, v_as_328_, v_lo_329_, v_hi_330_, v_w_331_, v_hlo_332_, v_hhi_333_);
lean_dec(v_hi_330_);
lean_dec(v_n_327_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(lean_object* v_n_335_, lean_object* v_lo_336_, lean_object* v_hi_337_, lean_object* v_hhi_338_, lean_object* v_pivot_339_, lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_k_342_, lean_object* v_ilo_343_, lean_object* v_ik_344_, lean_object* v_w_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_337_, v_pivot_339_, v_as_340_, v_i_341_, v_k_342_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___boxed(lean_object* v_n_347_, lean_object* v_lo_348_, lean_object* v_hi_349_, lean_object* v_hhi_350_, lean_object* v_pivot_351_, lean_object* v_as_352_, lean_object* v_i_353_, lean_object* v_k_354_, lean_object* v_ilo_355_, lean_object* v_ik_356_, lean_object* v_w_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0(v_n_347_, v_lo_348_, v_hi_349_, v_hhi_350_, v_pivot_351_, v_as_352_, v_i_353_, v_k_354_, v_ilo_355_, v_ik_356_, v_w_357_);
lean_dec(v_pivot_351_);
lean_dec(v_hi_349_);
lean_dec(v_lo_348_);
lean_dec(v_n_347_);
return v_res_358_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___f_360_; 
v___x_359_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_360_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_360_, 0, v___x_359_);
return v___f_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(lean_object* v___f_361_, lean_object* v_s_362_, lean_object* v_x_363_){
_start:
{
lean_object* v___f_364_; lean_object* v___x_365_; 
v___f_364_ = lean_obj_once(&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0, &l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0);
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_364_, v___f_361_, v_s_362_, v_x_363_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v___x_366_; 
v___x_366_ = lean_unsigned_to_nat(0u);
return v___x_366_;
}
else
{
lean_object* v_val_367_; 
v_val_367_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v___x_365_, 1);
return v_val_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(lean_object* v___f_368_, lean_object* v_s_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(v___f_368_, v_s_369_, v_x_370_);
lean_dec_ref(v_s_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(lean_object* v_a_376_, lean_object* v_b_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_dec(v_b_377_);
lean_dec(v_a_376_);
return v_x_378_;
}
else
{
lean_object* v_key_379_; lean_object* v_value_380_; lean_object* v_tail_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_393_; 
v_key_379_ = lean_ctor_get(v_x_378_, 0);
v_value_380_ = lean_ctor_get(v_x_378_, 1);
v_tail_381_ = lean_ctor_get(v_x_378_, 2);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_393_ == 0)
{
v___x_383_ = v_x_378_;
v_isShared_384_ = v_isSharedCheck_393_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_tail_381_);
lean_inc(v_value_380_);
lean_inc(v_key_379_);
lean_dec(v_x_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_393_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
uint8_t v___x_385_; 
v___x_385_ = lean_nat_dec_eq(v_key_379_, v_a_376_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_376_, v_b_377_, v_tail_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 2, v___x_386_);
v___x_388_ = v___x_383_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_key_379_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_value_380_);
lean_ctor_set(v_reuseFailAlloc_389_, 2, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec(v_value_380_);
lean_dec(v_key_379_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v_b_377_);
lean_ctor_set(v___x_383_, 0, v_a_376_);
v___x_391_ = v___x_383_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_376_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_b_377_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_tail_381_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(lean_object* v_m_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
lean_object* v_size_397_; lean_object* v_buckets_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_441_; 
v_size_397_ = lean_ctor_get(v_m_394_, 0);
v_buckets_398_ = lean_ctor_get(v_m_394_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_m_394_);
if (v_isSharedCheck_441_ == 0)
{
v___x_400_ = v_m_394_;
v_isShared_401_ = v_isSharedCheck_441_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_buckets_398_);
lean_inc(v_size_397_);
lean_dec(v_m_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_441_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v_fold_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v_bkt_415_; uint8_t v___x_416_; 
v___x_402_ = lean_array_get_size(v_buckets_398_);
v___x_403_ = lean_uint64_of_nat(v_a_395_);
v___x_404_ = 32ULL;
v___x_405_ = lean_uint64_shift_right(v___x_403_, v___x_404_);
v_fold_406_ = lean_uint64_xor(v___x_403_, v___x_405_);
v___x_407_ = 16ULL;
v___x_408_ = lean_uint64_shift_right(v_fold_406_, v___x_407_);
v___x_409_ = lean_uint64_xor(v_fold_406_, v___x_408_);
v___x_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = lean_usize_of_nat(v___x_402_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_sub(v___x_411_, v___x_412_);
v___x_414_ = lean_usize_land(v___x_410_, v___x_413_);
v_bkt_415_ = lean_array_uget_borrowed(v_buckets_398_, v___x_414_);
v___x_416_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_395_, v_bkt_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v_size_x27_418_; lean_object* v___x_419_; lean_object* v_buckets_x27_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_417_ = lean_unsigned_to_nat(1u);
v_size_x27_418_ = lean_nat_add(v_size_397_, v___x_417_);
lean_dec(v_size_397_);
lean_inc(v_bkt_415_);
v___x_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_419_, 0, v_a_395_);
lean_ctor_set(v___x_419_, 1, v_b_396_);
lean_ctor_set(v___x_419_, 2, v_bkt_415_);
v_buckets_x27_420_ = lean_array_uset(v_buckets_398_, v___x_414_, v___x_419_);
v___x_421_ = lean_unsigned_to_nat(4u);
v___x_422_ = lean_nat_mul(v_size_x27_418_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(3u);
v___x_424_ = lean_nat_div(v___x_422_, v___x_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_array_get_size(v_buckets_x27_420_);
v___x_426_ = lean_nat_dec_le(v___x_424_, v___x_425_);
lean_dec(v___x_424_);
if (v___x_426_ == 0)
{
lean_object* v_val_427_; lean_object* v___x_429_; 
v_val_427_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_420_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_val_427_);
lean_ctor_set(v___x_400_, 0, v_size_x27_418_);
v___x_429_ = v___x_400_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_size_x27_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_val_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v___x_432_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_buckets_x27_420_);
lean_ctor_set(v___x_400_, 0, v_size_x27_418_);
v___x_432_ = v___x_400_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_size_x27_418_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_buckets_x27_420_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v___x_434_; lean_object* v_buckets_x27_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
lean_inc(v_bkt_415_);
v___x_434_ = lean_box(0);
v_buckets_x27_435_ = lean_array_uset(v_buckets_398_, v___x_414_, v___x_434_);
v___x_436_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_395_, v_b_396_, v_bkt_415_);
v___x_437_ = lean_array_uset(v_buckets_x27_435_, v___x_414_, v___x_436_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_437_);
v___x_439_ = v___x_400_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_size_397_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(lean_object* v_as_442_, size_t v_sz_443_, size_t v_i_444_, lean_object* v_b_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_lt(v_i_444_, v_sz_443_);
if (v___x_446_ == 0)
{
return v_b_445_;
}
else
{
lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_462_; 
v_fst_447_ = lean_ctor_get(v_b_445_, 0);
v_snd_448_ = lean_ctor_get(v_b_445_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_b_445_);
if (v_isSharedCheck_462_ == 0)
{
v___x_450_ = v_b_445_;
v_isShared_451_ = v_isSharedCheck_462_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_snd_448_);
lean_inc(v_fst_447_);
lean_dec(v_b_445_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_462_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_a_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v_a_452_ = lean_array_uget_borrowed(v_as_442_, v_i_444_);
lean_inc(v_snd_448_);
lean_inc(v_a_452_);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_fst_447_, v_a_452_, v_snd_448_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_snd_448_, v___x_454_);
lean_dec(v_snd_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_455_);
lean_ctor_set(v___x_450_, 0, v___x_453_);
v___x_457_ = v___x_450_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
size_t v___x_458_; size_t v___x_459_; 
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_444_, v___x_458_);
v_i_444_ = v___x_459_;
v_b_445_ = v___x_457_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1___boxed(lean_object* v_as_463_, lean_object* v_sz_464_, lean_object* v_i_465_, lean_object* v_b_466_){
_start:
{
size_t v_sz_boxed_467_; size_t v_i_boxed_468_; lean_object* v_res_469_; 
v_sz_boxed_467_ = lean_unbox_usize(v_sz_464_);
lean_dec(v_sz_464_);
v_i_boxed_468_ = lean_unbox_usize(v_i_465_);
lean_dec(v_i_465_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_as_463_, v_sz_boxed_467_, v_i_boxed_468_, v_b_466_);
lean_dec_ref(v_as_463_);
return v_res_469_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__0(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = lean_unsigned_to_nat(16u);
v___x_472_ = lean_mk_array(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_old2new_475_; 
v___x_473_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__0, &l_Lean_Meta_Grind_mkVarRename___closed__0_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__0);
v___x_474_ = lean_unsigned_to_nat(0u);
v_old2new_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_old2new_475_, 0, v___x_474_);
lean_ctor_set(v_old2new_475_, 1, v___x_473_);
return v_old2new_475_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__2(void){
_start:
{
lean_object* v___x_476_; lean_object* v_old2new_477_; lean_object* v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v_old2new_477_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__1, &l_Lean_Meta_Grind_mkVarRename___closed__1_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__1);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_old2new_477_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object* v_new2old_479_){
_start:
{
lean_object* v___x_480_; size_t v_sz_481_; size_t v___x_482_; lean_object* v___x_483_; lean_object* v_fst_484_; 
v___x_480_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__2, &l_Lean_Meta_Grind_mkVarRename___closed__2_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__2);
v_sz_481_ = lean_array_size(v_new2old_479_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_new2old_479_, v_sz_481_, v___x_482_, v___x_480_);
v_fst_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_fst_484_);
lean_dec_ref(v___x_483_);
return v_fst_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object* v_new2old_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Meta_Grind_mkVarRename(v_new2old_485_);
lean_dec_ref(v_new2old_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object* v_00_u03b2_487_, lean_object* v_m_488_, lean_object* v_a_489_, lean_object* v_b_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_m_488_, v_a_489_, v_b_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0(lean_object* v_00_u03b2_492_, lean_object* v_a_493_, lean_object* v_b_494_, lean_object* v_x_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_493_, v_b_494_, v_x_495_);
return v___x_496_;
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
