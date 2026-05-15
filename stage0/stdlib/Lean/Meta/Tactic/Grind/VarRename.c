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
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_nbuckets_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_53_ = lean_array_get_size(v_data_52_);
v___x_54_ = lean_unsigned_to_nat(2u);
v_nbuckets_55_ = lean_nat_mul(v___x_53_, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_box(0);
v___x_58_ = lean_mk_array(v_nbuckets_55_, v___x_57_);
v___x_59_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v___x_56_, v_data_52_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(lean_object* v_m_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_size_63_; lean_object* v_buckets_64_; lean_object* v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v_bkt_78_; uint8_t v___x_79_; 
v_size_63_ = lean_ctor_get(v_m_60_, 0);
v_buckets_64_ = lean_ctor_get(v_m_60_, 1);
v___x_65_ = lean_array_get_size(v_buckets_64_);
v___x_66_ = lean_uint64_of_nat(v_a_61_);
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___x_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___x_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_65_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v_bkt_78_ = lean_array_uget_borrowed(v_buckets_64_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_61_, v_bkt_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_100_; 
lean_inc_ref(v_buckets_64_);
lean_inc(v_size_63_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_60_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_60_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_60_, 0);
lean_dec(v_unused_102_);
v___x_81_ = v_m_60_;
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v_size_x27_84_; lean_object* v___x_85_; lean_object* v_buckets_x27_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_size_x27_84_ = lean_nat_add(v_size_63_, v___x_83_);
lean_dec(v_size_63_);
lean_inc(v_bkt_78_);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v_a_61_);
lean_ctor_set(v___x_85_, 1, v_b_62_);
lean_ctor_set(v___x_85_, 2, v_bkt_78_);
v_buckets_x27_86_ = lean_array_uset(v_buckets_64_, v___x_77_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4u);
v___x_88_ = lean_nat_mul(v_size_x27_84_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_div(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_array_get_size(v_buckets_x27_86_);
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_86_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_val_93_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_95_ = v___x_81_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_buckets_x27_86_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_buckets_x27_86_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec(v_b_62_);
lean_dec(v_a_61_);
return v_m_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectVar(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_x_104_, v_x_103_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0(lean_object* v_00_u03b2_107_, lean_object* v_m_108_, lean_object* v_a_109_, lean_object* v_b_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0___redArg(v_m_108_, v_a_109_, v_b_110_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(lean_object* v_00_u03b2_112_, lean_object* v_a_113_, lean_object* v_x_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_113_, v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___boxed(lean_object* v_00_u03b2_116_, lean_object* v_a_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0(v_00_u03b2_116_, v_a_117_, v_x_118_);
lean_dec(v_x_118_);
lean_dec(v_a_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1(lean_object* v_00_u03b2_121_, lean_object* v_data_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_data_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_124_, lean_object* v_i_125_, lean_object* v_source_126_, lean_object* v_target_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2___redArg(v_i_125_, v_source_126_, v_target_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_130_, v_x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instAndThenVarCollector___lam__0(lean_object* v_c_u2081_133_, lean_object* v_c_u2082_134_, lean_object* v_s_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_1(v_c_u2081_133_, v_s_135_);
v___x_138_ = lean_apply_2(v_c_u2082_134_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(lean_object* v_k_141_, lean_object* v_a_142_, lean_object* v_b_143_, lean_object* v_acc_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_apply_2(v_k_141_, v_a_142_, v_acc_144_);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed(lean_object* v_k_147_, lean_object* v_a_148_, lean_object* v_b_149_, lean_object* v_acc_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Meta_Grind_collectMapVars___redArg___lam__0(v_k_147_, v_a_148_, v_b_149_, v_acc_150_);
lean_dec(v_b_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg___lam__1(lean_object* v___x_152_, lean_object* v___f_153_, lean_object* v_a_154_, lean_object* v_x_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_152_, v___f_153_, v_a_154_, v___y_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___redArg(lean_object* v_m_177_, lean_object* v_k_178_, lean_object* v_s_179_){
_start:
{
lean_object* v___x_180_; lean_object* v_buckets_181_; lean_object* v___f_182_; lean_object* v___f_183_; size_t v_sz_184_; size_t v___x_185_; lean_object* v___x_186_; 
v___x_180_ = ((lean_object*)(l_Lean_Meta_Grind_collectMapVars___redArg___closed__9));
v_buckets_181_ = lean_ctor_get(v_m_177_, 1);
lean_inc_ref(v_buckets_181_);
lean_dec_ref(v_m_177_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_182_, 0, v_k_178_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_collectMapVars___redArg___lam__1), 5, 2);
lean_closure_set(v___f_183_, 0, v___x_180_);
lean_closure_set(v___f_183_, 1, v___f_182_);
v_sz_184_ = lean_array_size(v_buckets_181_);
v___x_185_ = ((size_t)0ULL);
v___x_186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_180_, v_buckets_181_, v___f_183_, v_sz_184_, v___x_185_, v_s_179_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars(lean_object* v_00_u03b1_187_, lean_object* v_Expr_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_m_191_, lean_object* v_k_192_, lean_object* v_s_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Grind_collectMapVars___redArg(v_m_191_, v_k_192_, v_s_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMapVars___boxed(lean_object* v_00_u03b1_195_, lean_object* v_Expr_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_m_199_, lean_object* v_k_200_, lean_object* v_s_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_Grind_collectMapVars(v_00_u03b1_195_, v_Expr_196_, v_x_197_, v_x_198_, v_m_199_, v_k_200_, v_s_201_);
lean_dec_ref(v_x_198_);
lean_dec_ref(v_x_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(lean_object* v_x_203_, lean_object* v_x_204_){
_start:
{
if (lean_obj_tag(v_x_204_) == 0)
{
return v_x_203_;
}
else
{
lean_object* v_key_205_; lean_object* v_tail_206_; lean_object* v___x_207_; 
v_key_205_ = lean_ctor_get(v_x_204_, 0);
lean_inc(v_key_205_);
v_tail_206_ = lean_ctor_get(v_x_204_, 2);
lean_inc(v_tail_206_);
lean_dec_ref(v_x_204_);
v___x_207_ = lean_array_push(v_x_203_, v_key_205_);
v_x_203_ = v___x_207_;
v_x_204_ = v_tail_206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(lean_object* v_as_209_, size_t v_i_210_, size_t v_stop_211_, lean_object* v_b_212_){
_start:
{
uint8_t v___x_213_; 
v___x_213_ = lean_usize_dec_eq(v_i_210_, v_stop_211_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; size_t v___x_216_; size_t v___x_217_; 
v___x_214_ = lean_array_uget_borrowed(v_as_209_, v_i_210_);
lean_inc(v___x_214_);
v___x_215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Grind_FoundVars_toArray_spec__1(v_b_212_, v___x_214_);
v___x_216_ = ((size_t)1ULL);
v___x_217_ = lean_usize_add(v_i_210_, v___x_216_);
v_i_210_ = v___x_217_;
v_b_212_ = v___x_215_;
goto _start;
}
else
{
return v_b_212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2___boxed(lean_object* v_as_219_, lean_object* v_i_220_, lean_object* v_stop_221_, lean_object* v_b_222_){
_start:
{
size_t v_i_boxed_223_; size_t v_stop_boxed_224_; lean_object* v_res_225_; 
v_i_boxed_223_ = lean_unbox_usize(v_i_220_);
lean_dec(v_i_220_);
v_stop_boxed_224_ = lean_unbox_usize(v_stop_221_);
lean_dec(v_stop_221_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_as_219_, v_i_boxed_223_, v_stop_boxed_224_, v_b_222_);
lean_dec_ref(v_as_219_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(lean_object* v_hi_226_, lean_object* v_pivot_227_, lean_object* v_as_228_, lean_object* v_i_229_, lean_object* v_k_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = lean_nat_dec_lt(v_k_230_, v_hi_226_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_k_230_);
v___x_232_ = lean_array_fswap(v_as_228_, v_i_229_, v_hi_226_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v_i_229_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_array_fget_borrowed(v_as_228_, v_k_230_);
v___x_235_ = lean_nat_dec_lt(v___x_234_, v_pivot_227_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_k_230_, v___x_236_);
lean_dec(v_k_230_);
v_k_230_ = v___x_237_;
goto _start;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_239_ = lean_array_fswap(v_as_228_, v_i_229_, v_k_230_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_i_229_, v___x_240_);
lean_dec(v_i_229_);
v___x_242_ = lean_nat_add(v_k_230_, v___x_240_);
lean_dec(v_k_230_);
v_as_228_ = v___x_239_;
v_i_229_ = v___x_241_;
v_k_230_ = v___x_242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_hi_244_, lean_object* v_pivot_245_, lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_k_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_244_, v_pivot_245_, v_as_246_, v_i_247_, v_k_248_);
lean_dec(v_pivot_245_);
lean_dec(v_hi_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(lean_object* v_n_250_, lean_object* v_as_251_, lean_object* v_lo_252_, lean_object* v_hi_253_){
_start:
{
lean_object* v___y_255_; uint8_t v___x_265_; 
v___x_265_ = lean_nat_dec_lt(v_lo_252_, v_hi_253_);
if (v___x_265_ == 0)
{
lean_dec(v_lo_252_);
return v_as_251_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_mid_268_; lean_object* v___y_270_; lean_object* v___y_276_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_266_ = lean_nat_add(v_lo_252_, v_hi_253_);
v___x_267_ = lean_unsigned_to_nat(1u);
v_mid_268_ = lean_nat_shiftr(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
v___x_281_ = lean_array_fget_borrowed(v_as_251_, v_mid_268_);
v___x_282_ = lean_array_fget_borrowed(v_as_251_, v_lo_252_);
v___x_283_ = lean_nat_dec_lt(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
v___y_276_ = v_as_251_;
goto v___jp_275_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_array_fswap(v_as_251_, v_lo_252_, v_mid_268_);
v___y_276_ = v___x_284_;
goto v___jp_275_;
}
v___jp_269_:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_array_fget_borrowed(v___y_270_, v_mid_268_);
v___x_272_ = lean_array_fget_borrowed(v___y_270_, v_hi_253_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_mid_268_);
v___y_255_ = v___y_270_;
goto v___jp_254_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_array_fswap(v___y_270_, v_mid_268_, v_hi_253_);
lean_dec(v_mid_268_);
v___y_255_ = v___x_274_;
goto v___jp_254_;
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = lean_array_fget_borrowed(v___y_276_, v_hi_253_);
v___x_278_ = lean_array_fget_borrowed(v___y_276_, v_lo_252_);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
v___y_270_ = v___y_276_;
goto v___jp_269_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = lean_array_fswap(v___y_276_, v_lo_252_, v_hi_253_);
v___y_270_ = v___x_280_;
goto v___jp_269_;
}
}
}
v___jp_254_:
{
lean_object* v_pivot_256_; lean_object* v___x_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; uint8_t v___x_260_; 
v_pivot_256_ = lean_array_fget(v___y_255_, v_hi_253_);
lean_inc_n(v_lo_252_, 2);
v___x_257_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0_spec__0___redArg(v_hi_253_, v_pivot_256_, v___y_255_, v_lo_252_, v_lo_252_);
lean_dec(v_pivot_256_);
v_fst_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_fst_258_);
v_snd_259_ = lean_ctor_get(v___x_257_, 1);
lean_inc(v_snd_259_);
lean_dec_ref(v___x_257_);
v___x_260_ = lean_nat_dec_le(v_hi_253_, v_fst_258_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_250_, v_snd_259_, v_lo_252_, v_fst_258_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_fst_258_, v___x_262_);
lean_dec(v_fst_258_);
v_as_251_ = v___x_261_;
v_lo_252_ = v___x_263_;
goto _start;
}
else
{
lean_dec(v_fst_258_);
lean_dec(v_lo_252_);
return v_snd_259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(lean_object* v_n_285_, lean_object* v_as_286_, lean_object* v_lo_287_, lean_object* v_hi_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_n_285_, v_as_286_, v_lo_287_, v_hi_288_);
lean_dec(v_hi_288_);
lean_dec(v_n_285_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object* v_s_290_){
_start:
{
lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_300_; lean_object* v_size_307_; lean_object* v_buckets_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_size_307_ = lean_ctor_get(v_s_290_, 0);
v_buckets_308_ = lean_ctor_get(v_s_290_, 1);
v___x_309_ = lean_mk_empty_array_with_capacity(v_size_307_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_array_get_size(v_buckets_308_);
v___x_312_ = lean_nat_dec_lt(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
v___y_300_ = v___x_309_;
goto v___jp_299_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = lean_nat_dec_le(v___x_311_, v___x_311_);
if (v___x_313_ == 0)
{
if (v___x_312_ == 0)
{
v___y_300_ = v___x_309_;
goto v___jp_299_;
}
else
{
size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((size_t)0ULL);
v___x_315_ = lean_usize_of_nat(v___x_311_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_308_, v___x_314_, v___x_315_, v___x_309_);
v___y_300_ = v___x_316_;
goto v___jp_299_;
}
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((size_t)0ULL);
v___x_318_ = lean_usize_of_nat(v___x_311_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_308_, v___x_317_, v___x_318_, v___x_309_);
v___y_300_ = v___x_319_;
goto v___jp_299_;
}
}
v___jp_291_:
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_le(v___y_295_, v___y_294_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; 
lean_dec(v___y_294_);
lean_inc(v___y_295_);
v___x_297_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_292_, v___y_293_, v___y_295_, v___y_295_);
lean_dec(v___y_295_);
lean_dec(v___y_292_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_292_, v___y_293_, v___y_295_, v___y_294_);
lean_dec(v___y_294_);
lean_dec(v___y_292_);
return v___x_298_;
}
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_array_get_size(v___y_300_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_nat_dec_eq(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_sub(v___x_301_, v___x_304_);
v___x_306_ = lean_nat_dec_le(v___x_302_, v___x_305_);
if (v___x_306_ == 0)
{
lean_inc(v___x_305_);
v___y_292_ = v___x_301_;
v___y_293_ = v___y_300_;
v___y_294_ = v___x_305_;
v___y_295_ = v___x_305_;
goto v___jp_291_;
}
else
{
v___y_292_ = v___x_301_;
v___y_293_ = v___y_300_;
v___y_294_ = v___x_305_;
v___y_295_ = v___x_302_;
goto v___jp_291_;
}
}
else
{
return v___y_300_;
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
lean_dec_ref(v___x_368_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(lean_object* v_as_445_, size_t v_sz_446_, size_t v_i_447_, lean_object* v_b_448_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1___boxed(lean_object* v_as_466_, lean_object* v_sz_467_, lean_object* v_i_468_, lean_object* v_b_469_){
_start:
{
size_t v_sz_boxed_470_; size_t v_i_boxed_471_; lean_object* v_res_472_; 
v_sz_boxed_470_ = lean_unbox_usize(v_sz_467_);
lean_dec(v_sz_467_);
v_i_boxed_471_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_as_466_, v_sz_boxed_470_, v_i_boxed_471_, v_b_469_);
lean_dec_ref(v_as_466_);
return v_res_472_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_unsigned_to_nat(16u);
v___x_475_ = lean_mk_array(v___x_474_, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_old2new_478_; 
v___x_476_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__0, &l_Lean_Meta_Grind_mkVarRename___closed__0_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__0);
v___x_477_ = lean_unsigned_to_nat(0u);
v_old2new_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_old2new_478_, 0, v___x_477_);
lean_ctor_set(v_old2new_478_, 1, v___x_476_);
return v_old2new_478_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__2(void){
_start:
{
lean_object* v___x_479_; lean_object* v_old2new_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v_old2new_480_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__1, &l_Lean_Meta_Grind_mkVarRename___closed__1_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__1);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_old2new_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object* v_new2old_482_){
_start:
{
lean_object* v___x_483_; size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v_fst_487_; 
v___x_483_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__2, &l_Lean_Meta_Grind_mkVarRename___closed__2_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__2);
v_sz_484_ = lean_array_size(v_new2old_482_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_new2old_482_, v_sz_484_, v___x_485_, v___x_483_);
v_fst_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_fst_487_);
lean_dec_ref(v___x_486_);
return v_fst_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object* v_new2old_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Meta_Grind_mkVarRename(v_new2old_488_);
lean_dec_ref(v_new2old_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object* v_00_u03b2_490_, lean_object* v_m_491_, lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_m_491_, v_a_492_, v_b_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0(lean_object* v_00_u03b2_495_, lean_object* v_a_496_, lean_object* v_b_497_, lean_object* v_x_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_496_, v_b_497_, v_x_498_);
return v___x_499_;
}
}
lean_object* runtime_initialize_Init_Data_Array_QSort(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
