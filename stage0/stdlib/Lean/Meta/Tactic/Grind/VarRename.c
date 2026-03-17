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
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(lean_object* v_as_227_, lean_object* v_lo_228_, lean_object* v_hi_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = lean_nat_dec_lt(v_lo_228_, v_hi_229_);
if (v___x_230_ == 0)
{
lean_dec(v_lo_228_);
return v_as_227_;
}
else
{
lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v_fst_233_; lean_object* v_snd_234_; uint8_t v___x_235_; 
v___f_231_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___closed__0));
lean_inc(v_lo_228_);
v___x_232_ = l_Array_qpartition___redArg(v_as_227_, v___f_231_, v_lo_228_, v_hi_229_);
v_fst_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_fst_233_);
v_snd_234_ = lean_ctor_get(v___x_232_, 1);
lean_inc(v_snd_234_);
lean_dec_ref(v___x_232_);
v___x_235_ = lean_nat_dec_le(v_hi_229_, v_fst_233_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_snd_234_, v_lo_228_, v_fst_233_);
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_fst_233_, v___x_237_);
lean_dec(v_fst_233_);
v_as_227_ = v___x_236_;
v_lo_228_ = v___x_238_;
goto _start;
}
else
{
lean_dec(v_fst_233_);
lean_dec(v_lo_228_);
return v_snd_234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg___boxed(lean_object* v_as_240_, lean_object* v_lo_241_, lean_object* v_hi_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_as_240_, v_lo_241_, v_hi_242_);
lean_dec(v_hi_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray(lean_object* v_s_244_){
_start:
{
lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_254_; lean_object* v_size_261_; lean_object* v_buckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_size_261_ = lean_ctor_get(v_s_244_, 0);
v_buckets_262_ = lean_ctor_get(v_s_244_, 1);
v___x_263_ = lean_mk_empty_array_with_capacity(v_size_261_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_array_get_size(v_buckets_262_);
v___x_266_ = lean_nat_dec_lt(v___x_264_, v___x_265_);
if (v___x_266_ == 0)
{
v___y_254_ = v___x_263_;
goto v___jp_253_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = lean_nat_dec_le(v___x_265_, v___x_265_);
if (v___x_267_ == 0)
{
if (v___x_266_ == 0)
{
v___y_254_ = v___x_263_;
goto v___jp_253_;
}
else
{
size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((size_t)0ULL);
v___x_269_ = lean_usize_of_nat(v___x_265_);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_262_, v___x_268_, v___x_269_, v___x_263_);
v___y_254_ = v___x_270_;
goto v___jp_253_;
}
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((size_t)0ULL);
v___x_272_ = lean_usize_of_nat(v___x_265_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_FoundVars_toArray_spec__2(v_buckets_262_, v___x_271_, v___x_272_, v___x_263_);
v___y_254_ = v___x_273_;
goto v___jp_253_;
}
}
v___jp_245_:
{
uint8_t v___x_250_; 
lean_dec(v___y_246_);
v___x_250_ = lean_nat_dec_le(v___y_249_, v___y_248_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec(v___y_248_);
lean_inc(v___y_249_);
v___x_251_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_247_, v___y_249_, v___y_249_);
lean_dec(v___y_249_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v___y_247_, v___y_249_, v___y_248_);
lean_dec(v___y_248_);
return v___x_252_;
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_array_get_size(v___y_254_);
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_nat_dec_eq(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_sub(v___x_255_, v___x_258_);
v___x_260_ = lean_nat_dec_le(v___x_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_inc(v___x_259_);
v___y_246_ = v___x_255_;
v___y_247_ = v___y_254_;
v___y_248_ = v___x_259_;
v___y_249_ = v___x_259_;
goto v___jp_245_;
}
else
{
v___y_246_ = v___x_255_;
v___y_247_ = v___y_254_;
v___y_248_ = v___x_259_;
v___y_249_ = v___x_256_;
goto v___jp_245_;
}
}
else
{
return v___y_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_FoundVars_toArray___boxed(lean_object* v_s_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Meta_Grind_FoundVars_toArray(v_s_274_);
lean_dec_ref(v_s_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(lean_object* v_n_276_, lean_object* v_as_277_, lean_object* v_lo_278_, lean_object* v_hi_279_, lean_object* v_w_280_, lean_object* v_hlo_281_, lean_object* v_hhi_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___redArg(v_as_277_, v_lo_278_, v_hi_279_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0___boxed(lean_object* v_n_284_, lean_object* v_as_285_, lean_object* v_lo_286_, lean_object* v_hi_287_, lean_object* v_w_288_, lean_object* v_hlo_289_, lean_object* v_hhi_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Grind_FoundVars_toArray_spec__0(v_n_284_, v_as_285_, v_lo_286_, v_hi_287_, v_w_288_, v_hlo_289_, v_hhi_290_);
lean_dec(v_hi_287_);
lean_dec(v_n_284_);
return v_res_291_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0(void){
_start:
{
lean_object* v___x_292_; lean_object* v___f_293_; 
v___x_292_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_293_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_293_, 0, v___x_292_);
return v___f_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(lean_object* v___f_294_, lean_object* v_s_295_, lean_object* v_x_296_){
_start:
{
lean_object* v___f_297_; lean_object* v___x_298_; 
v___f_297_ = lean_obj_once(&l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0, &l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___closed__0);
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_297_, v___f_294_, v_s_295_, v_x_296_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_unsigned_to_nat(0u);
return v___x_299_;
}
else
{
lean_object* v_val_300_; 
v_val_300_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_val_300_);
lean_dec_ref(v___x_298_);
return v_val_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0___boxed(lean_object* v___f_301_, lean_object* v_s_302_, lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_instCoeFunVarRenameForallVar___lam__0(v___f_301_, v_s_302_, v_x_303_);
lean_dec_ref(v_s_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(lean_object* v_a_309_, lean_object* v_b_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_dec(v_b_310_);
lean_dec(v_a_309_);
return v_x_311_;
}
else
{
lean_object* v_key_312_; lean_object* v_value_313_; lean_object* v_tail_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_326_; 
v_key_312_ = lean_ctor_get(v_x_311_, 0);
v_value_313_ = lean_ctor_get(v_x_311_, 1);
v_tail_314_ = lean_ctor_get(v_x_311_, 2);
v_isSharedCheck_326_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_326_ == 0)
{
v___x_316_ = v_x_311_;
v_isShared_317_ = v_isSharedCheck_326_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_tail_314_);
lean_inc(v_value_313_);
lean_inc(v_key_312_);
lean_dec(v_x_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_326_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_eq(v_key_312_, v_a_309_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_309_, v_b_310_, v_tail_314_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 2, v___x_319_);
v___x_321_ = v___x_316_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_key_312_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_value_313_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
else
{
lean_object* v___x_324_; 
lean_dec(v_value_313_);
lean_dec(v_key_312_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 1, v_b_310_);
lean_ctor_set(v___x_316_, 0, v_a_309_);
v___x_324_ = v___x_316_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_309_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_b_310_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_tail_314_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(lean_object* v_m_327_, lean_object* v_a_328_, lean_object* v_b_329_){
_start:
{
lean_object* v_size_330_; lean_object* v_buckets_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_374_; 
v_size_330_ = lean_ctor_get(v_m_327_, 0);
v_buckets_331_ = lean_ctor_get(v_m_327_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_m_327_);
if (v_isSharedCheck_374_ == 0)
{
v___x_333_ = v_m_327_;
v_isShared_334_ = v_isSharedCheck_374_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_buckets_331_);
lean_inc(v_size_330_);
lean_dec(v_m_327_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_374_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v_bkt_348_; uint8_t v___x_349_; 
v___x_335_ = lean_array_get_size(v_buckets_331_);
v___x_336_ = lean_uint64_of_nat(v_a_328_);
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___x_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___x_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_335_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v_bkt_348_ = lean_array_uget_borrowed(v_buckets_331_, v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__0___redArg(v_a_328_, v_bkt_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v_size_x27_351_; lean_object* v___x_352_; lean_object* v_buckets_x27_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v_size_x27_351_ = lean_nat_add(v_size_330_, v___x_350_);
lean_dec(v_size_330_);
lean_inc(v_bkt_348_);
v___x_352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_352_, 0, v_a_328_);
lean_ctor_set(v___x_352_, 1, v_b_329_);
lean_ctor_set(v___x_352_, 2, v_bkt_348_);
v_buckets_x27_353_ = lean_array_uset(v_buckets_331_, v___x_347_, v___x_352_);
v___x_354_ = lean_unsigned_to_nat(4u);
v___x_355_ = lean_nat_mul(v_size_x27_351_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(3u);
v___x_357_ = lean_nat_div(v___x_355_, v___x_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_array_get_size(v_buckets_x27_353_);
v___x_359_ = lean_nat_dec_le(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
if (v___x_359_ == 0)
{
lean_object* v_val_360_; lean_object* v___x_362_; 
v_val_360_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Grind_collectVar_spec__0_spec__1___redArg(v_buckets_x27_353_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_val_360_);
lean_ctor_set(v___x_333_, 0, v_size_x27_351_);
v___x_362_ = v___x_333_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_size_x27_351_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_val_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
else
{
lean_object* v___x_365_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_buckets_x27_353_);
lean_ctor_set(v___x_333_, 0, v_size_x27_351_);
v___x_365_ = v___x_333_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_size_x27_351_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_buckets_x27_353_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v___x_367_; lean_object* v_buckets_x27_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
lean_inc(v_bkt_348_);
v___x_367_ = lean_box(0);
v_buckets_x27_368_ = lean_array_uset(v_buckets_331_, v___x_347_, v___x_367_);
v___x_369_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_328_, v_b_329_, v_bkt_348_);
v___x_370_ = lean_array_uset(v_buckets_x27_368_, v___x_347_, v___x_369_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_370_);
v___x_372_ = v___x_333_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_size_330_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(lean_object* v_as_375_, size_t v_sz_376_, size_t v_i_377_, lean_object* v_b_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_lt(v_i_377_, v_sz_376_);
if (v___x_379_ == 0)
{
return v_b_378_;
}
else
{
lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_395_; 
v_fst_380_ = lean_ctor_get(v_b_378_, 0);
v_snd_381_ = lean_ctor_get(v_b_378_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_b_378_);
if (v_isSharedCheck_395_ == 0)
{
v___x_383_ = v_b_378_;
v_isShared_384_ = v_isSharedCheck_395_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_snd_381_);
lean_inc(v_fst_380_);
lean_dec(v_b_378_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_395_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v_a_385_ = lean_array_uget_borrowed(v_as_375_, v_i_377_);
lean_inc(v_snd_381_);
lean_inc(v_a_385_);
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_fst_380_, v_a_385_, v_snd_381_);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_snd_381_, v___x_387_);
lean_dec(v_snd_381_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 1, v___x_388_);
lean_ctor_set(v___x_383_, 0, v___x_386_);
v___x_390_ = v___x_383_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_377_, v___x_391_);
v_i_377_ = v___x_392_;
v_b_378_ = v___x_390_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1___boxed(lean_object* v_as_396_, lean_object* v_sz_397_, lean_object* v_i_398_, lean_object* v_b_399_){
_start:
{
size_t v_sz_boxed_400_; size_t v_i_boxed_401_; lean_object* v_res_402_; 
v_sz_boxed_400_ = lean_unbox_usize(v_sz_397_);
lean_dec(v_sz_397_);
v_i_boxed_401_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_res_402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_as_396_, v_sz_boxed_400_, v_i_boxed_401_, v_b_399_);
lean_dec_ref(v_as_396_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__0(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_box(0);
v___x_404_ = lean_unsigned_to_nat(16u);
v___x_405_ = lean_mk_array(v___x_404_, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_old2new_408_; 
v___x_406_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__0, &l_Lean_Meta_Grind_mkVarRename___closed__0_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__0);
v___x_407_ = lean_unsigned_to_nat(0u);
v_old2new_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_old2new_408_, 0, v___x_407_);
lean_ctor_set(v_old2new_408_, 1, v___x_406_);
return v_old2new_408_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkVarRename___closed__2(void){
_start:
{
lean_object* v___x_409_; lean_object* v_old2new_410_; lean_object* v___x_411_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v_old2new_410_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__1, &l_Lean_Meta_Grind_mkVarRename___closed__1_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__1);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_old2new_410_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename(lean_object* v_new2old_412_){
_start:
{
lean_object* v___x_413_; size_t v_sz_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v_fst_417_; 
v___x_413_ = lean_obj_once(&l_Lean_Meta_Grind_mkVarRename___closed__2, &l_Lean_Meta_Grind_mkVarRename___closed__2_once, _init_l_Lean_Meta_Grind_mkVarRename___closed__2);
v_sz_414_ = lean_array_size(v_new2old_412_);
v___x_415_ = ((size_t)0ULL);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_mkVarRename_spec__1(v_new2old_412_, v_sz_414_, v___x_415_, v___x_413_);
v_fst_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_fst_417_);
lean_dec_ref(v___x_416_);
return v_fst_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkVarRename___boxed(lean_object* v_new2old_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_Grind_mkVarRename(v_new2old_418_);
lean_dec_ref(v_new2old_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0(lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0___redArg(v_m_421_, v_a_422_, v_b_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0(lean_object* v_00_u03b2_425_, lean_object* v_a_426_, lean_object* v_b_427_, lean_object* v_x_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_mkVarRename_spec__0_spec__0___redArg(v_a_426_, v_b_427_, v_x_428_);
return v___x_429_;
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
