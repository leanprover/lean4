// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Defs
// Imports: public import Init.Data.Array.Lemmas public import Std.Data.DHashMap.RawDef public import Std.Data.Internal.List.Defs public import Std.Data.DHashMap.Internal.Index public import Init.Data.Nat.Power2.Basic import Init.Data.Nat.Power2.Lemmas import Init.Data.List.Impl import Init.Omega
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
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCastD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_toList___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_DHashMap_Internal_toListModel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DHashMap_Internal_toListModel___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_toListModel___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value;
static const lean_closure_object l_Std_DHashMap_Internal_computeSize___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_computeSize___redArg___closed__10 = (const lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_reinsertAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_reinsertAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_computeSize___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity(lean_object* v_capacity_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_2_ = lean_unsigned_to_nat(4u);
v___x_3_ = lean_nat_mul(v_capacity_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(3u);
v___x_5_ = lean_nat_div(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity___boxed(lean_object* v_capacity_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_numBucketsForCapacity(v_capacity_6_);
lean_dec(v_capacity_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
if (lean_obj_tag(v_a_8_) == 0)
{
lean_object* v___x_10_; 
v___x_10_ = lean_array_to_list(v_a_9_);
return v___x_10_;
}
else
{
lean_object* v_head_11_; lean_object* v_tail_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_head_11_ = lean_ctor_get(v_a_8_, 0);
v_tail_12_ = lean_ctor_get(v_a_8_, 1);
v___x_13_ = l_Std_DHashMap_Internal_AssocList_toList___redArg(v_head_11_);
v___x_14_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_9_, v___x_13_);
v_a_8_ = v_tail_12_;
v_a_9_ = v___x_14_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg___boxed(lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v_a_16_, v_a_17_);
lean_dec(v_a_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel___redArg(lean_object* v_buckets_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_array_to_list(v_buckets_21_);
v___x_23_ = ((lean_object*)(l_Std_DHashMap_Internal_toListModel___redArg___closed__0));
v___x_24_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_toListModel(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_buckets_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_a_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___redArg(v_a_31_, v_a_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0___boxed(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Std_DHashMap_Internal_toListModel_spec__0(v_00_u03b1_34_, v_00_u03b2_35_, v_a_36_, v_a_37_);
lean_dec(v_a_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0(lean_object* v_x1_39_, lean_object* v_x2_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v_x2_40_);
v___x_42_ = lean_nat_add(v_x1_39_, v___x_41_);
lean_dec(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg___lam__0___boxed(lean_object* v_x1_43_, lean_object* v_x2_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_DHashMap_Internal_computeSize___redArg___lam__0(v_x1_43_, v_x2_44_);
lean_dec(v_x2_44_);
lean_dec(v_x1_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize___redArg(lean_object* v_buckets_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_array_get_size(v_buckets_66_);
v___x_69_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_70_ = lean_nat_dec_lt(v___x_67_, v___x_68_);
if (v___x_70_ == 0)
{
lean_dec_ref(v_buckets_66_);
return v___x_67_;
}
else
{
lean_object* v___f_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; 
v___f_71_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_72_ = ((size_t)0ULL);
v___x_73_ = lean_usize_of_nat(v___x_68_);
v___x_74_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_71_, v_buckets_66_, v___x_72_, v___x_73_, v___x_67_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_buckets_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_array_get_size(v_buckets_77_);
v___x_80_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_81_ = lean_nat_dec_lt(v___x_78_, v___x_79_);
if (v___x_81_ == 0)
{
lean_dec_ref(v_buckets_77_);
return v___x_78_;
}
else
{
lean_object* v___f_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; 
v___f_82_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_83_ = ((size_t)0ULL);
v___x_84_ = lean_usize_of_nat(v___x_79_);
v___x_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_80_, v___f_82_, v_buckets_77_, v___x_83_, v___x_84_, v___x_78_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(lean_object* v_capacity_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_unsigned_to_nat(4u);
v___x_89_ = lean_nat_mul(v_capacity_86_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = lean_nat_div(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = l_Nat_nextPowerOfTwo(v___x_91_);
lean_dec(v___x_91_);
v___x_93_ = lean_box(0);
v___x_94_ = lean_mk_array(v___x_92_, v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_87_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(v_capacity_96_);
lean_dec(v_capacity_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_capacity_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_unsigned_to_nat(4u);
v___x_103_ = lean_nat_mul(v_capacity_100_, v___x_102_);
v___x_104_ = lean_unsigned_to_nat(3u);
v___x_105_ = lean_nat_div(v___x_103_, v___x_104_);
lean_dec(v___x_103_);
v___x_106_ = l_Nat_nextPowerOfTwo(v___x_105_);
lean_dec(v___x_105_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_mk_array(v___x_106_, v___x_107_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_101_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___boxed(lean_object* v_00_u03b1_110_, lean_object* v_00_u03b2_111_, lean_object* v_capacity_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(v_00_u03b1_110_, v_00_u03b2_111_, v_capacity_112_);
lean_dec(v_capacity_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_reinsertAux___redArg(lean_object* v_hash_114_, lean_object* v_data_115_, lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v___x_123_; uint64_t v_fold_124_; uint64_t v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_118_ = lean_array_get_size(v_data_115_);
lean_inc(v_a_116_);
v___x_119_ = lean_apply_1(v_hash_114_, v_a_116_);
v___x_120_ = 32ULL;
v___x_121_ = lean_unbox_uint64(v___x_119_);
v___x_122_ = lean_uint64_shift_right(v___x_121_, v___x_120_);
v___x_123_ = lean_unbox_uint64(v___x_119_);
lean_dec_ref(v___x_119_);
v_fold_124_ = lean_uint64_xor(v___x_123_, v___x_122_);
v___x_125_ = 16ULL;
v___x_126_ = lean_uint64_shift_right(v_fold_124_, v___x_125_);
v___x_127_ = lean_uint64_xor(v_fold_124_, v___x_126_);
v___x_128_ = lean_uint64_to_usize(v___x_127_);
v___x_129_ = lean_usize_of_nat(v___x_118_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_sub(v___x_129_, v___x_130_);
v___x_132_ = lean_usize_land(v___x_128_, v___x_131_);
v___x_133_ = lean_array_uget_borrowed(v_data_115_, v___x_132_);
lean_inc(v___x_133_);
v___x_134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_134_, 0, v_a_116_);
lean_ctor_set(v___x_134_, 1, v_b_117_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
v___x_135_ = lean_array_uset(v_data_115_, v___x_132_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_reinsertAux(lean_object* v_00_u03b1_136_, lean_object* v_00_u03b2_137_, lean_object* v_hash_138_, lean_object* v_data_139_, lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint64_t v___x_144_; uint64_t v___x_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v_fold_148_; uint64_t v___x_149_; uint64_t v___x_150_; uint64_t v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; size_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_142_ = lean_array_get_size(v_data_139_);
lean_inc(v_a_140_);
v___x_143_ = lean_apply_1(v_hash_138_, v_a_140_);
v___x_144_ = 32ULL;
v___x_145_ = lean_unbox_uint64(v___x_143_);
v___x_146_ = lean_uint64_shift_right(v___x_145_, v___x_144_);
v___x_147_ = lean_unbox_uint64(v___x_143_);
lean_dec_ref(v___x_143_);
v_fold_148_ = lean_uint64_xor(v___x_147_, v___x_146_);
v___x_149_ = 16ULL;
v___x_150_ = lean_uint64_shift_right(v_fold_148_, v___x_149_);
v___x_151_ = lean_uint64_xor(v_fold_148_, v___x_150_);
v___x_152_ = lean_uint64_to_usize(v___x_151_);
v___x_153_ = lean_usize_of_nat(v___x_142_);
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_sub(v___x_153_, v___x_154_);
v___x_156_ = lean_usize_land(v___x_152_, v___x_155_);
v___x_157_ = lean_array_uget_borrowed(v_data_139_, v___x_156_);
lean_inc(v___x_157_);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v_a_140_);
lean_ctor_set(v___x_158_, 1, v_b_141_);
lean_ctor_set(v___x_158_, 2, v___x_157_);
v___x_159_ = lean_array_uset(v_data_139_, v___x_156_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0(lean_object* v_inst_160_, lean_object* v_x1_161_, lean_object* v_x2_162_, lean_object* v_x3_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; uint64_t v___x_169_; uint64_t v_fold_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_164_ = lean_array_get_size(v_x1_161_);
lean_inc(v_x2_162_);
v___x_165_ = lean_apply_1(v_inst_160_, v_x2_162_);
v___x_166_ = 32ULL;
v___x_167_ = lean_unbox_uint64(v___x_165_);
v___x_168_ = lean_uint64_shift_right(v___x_167_, v___x_166_);
v___x_169_ = lean_unbox_uint64(v___x_165_);
lean_dec_ref(v___x_165_);
v_fold_170_ = lean_uint64_xor(v___x_169_, v___x_168_);
v___x_171_ = 16ULL;
v___x_172_ = lean_uint64_shift_right(v_fold_170_, v___x_171_);
v___x_173_ = lean_uint64_xor(v_fold_170_, v___x_172_);
v___x_174_ = lean_uint64_to_usize(v___x_173_);
v___x_175_ = lean_usize_of_nat(v___x_164_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_sub(v___x_175_, v___x_176_);
v___x_178_ = lean_usize_land(v___x_174_, v___x_177_);
v___x_179_ = lean_array_uget_borrowed(v_x1_161_, v___x_178_);
lean_inc(v___x_179_);
v___x_180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_180_, 0, v_x2_162_);
lean_ctor_set(v___x_180_, 1, v_x3_163_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v___x_181_ = lean_array_uset(v_x1_161_, v___x_178_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(lean_object* v_inst_182_, lean_object* v_i_183_, lean_object* v_source_184_, lean_object* v_target_185_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_array_get_size(v_source_184_);
v___x_187_ = lean_nat_dec_lt(v_i_183_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec_ref(v_source_184_);
lean_dec(v_i_183_);
lean_dec_ref(v_inst_182_);
return v_target_185_;
}
else
{
lean_object* v___f_188_; lean_object* v_es_189_; lean_object* v___x_190_; lean_object* v_source_191_; lean_object* v___x_192_; lean_object* v_target_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
lean_inc_ref(v_inst_182_);
v___f_188_ = lean_alloc_closure((void*)(l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0), 4, 1);
lean_closure_set(v___f_188_, 0, v_inst_182_);
v_es_189_ = lean_array_fget(v_source_184_, v_i_183_);
v___x_190_ = lean_box(0);
v_source_191_ = lean_array_fset(v_source_184_, v_i_183_, v___x_190_);
v___x_192_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_target_193_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_192_, v___f_188_, v_target_185_, v_es_189_);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_i_183_, v___x_194_);
lean_dec(v_i_183_);
v_i_183_ = v___x_195_;
v_source_184_ = v_source_191_;
v_target_185_ = v_target_193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_, lean_object* v_inst_199_, lean_object* v_i_200_, lean_object* v_source_201_, lean_object* v_target_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(v_inst_199_, v_i_200_, v_source_201_, v_target_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object* v_inst_204_, lean_object* v_data_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_nbuckets_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_206_ = lean_array_get_size(v_data_205_);
v___x_207_ = lean_unsigned_to_nat(2u);
v_nbuckets_208_ = lean_nat_mul(v___x_206_, v___x_207_);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_box(0);
v___x_211_ = lean_mk_array(v_nbuckets_208_, v___x_210_);
v___x_212_ = lean_array_propagate_mark(v_data_205_, v___x_211_);
v___x_213_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(v_inst_204_, v___x_209_, v_data_205_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_inst_216_, lean_object* v_data_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_216_, v_data_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___redArg(lean_object* v_inst_219_, lean_object* v_m_220_){
_start:
{
lean_object* v_size_221_; lean_object* v_buckets_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_size_221_ = lean_ctor_get(v_m_220_, 0);
v_buckets_222_ = lean_ctor_get(v_m_220_, 1);
v___x_223_ = lean_unsigned_to_nat(4u);
v___x_224_ = lean_nat_mul(v_size_221_, v___x_223_);
v___x_225_ = lean_unsigned_to_nat(3u);
v___x_226_ = lean_nat_div(v___x_224_, v___x_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_array_get_size(v_buckets_222_);
v___x_228_ = lean_nat_dec_le(v___x_226_, v___x_227_);
lean_dec(v___x_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
lean_inc_ref(v_buckets_222_);
lean_inc(v_size_221_);
v_isSharedCheck_236_ = !lean_is_exclusive(v_m_220_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_237_ = lean_ctor_get(v_m_220_, 1);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_m_220_, 0);
lean_dec(v_unused_238_);
v___x_230_ = v_m_220_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_dec(v_m_220_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_val_232_; lean_object* v___x_234_; 
v_val_232_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_219_, v_buckets_222_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v_val_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_size_221_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_val_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_dec_ref(v_inst_219_);
return v_m_220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(lean_object* v_00_u03b1_239_, lean_object* v_00_u03b2_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_m_243_){
_start:
{
lean_object* v_size_244_; lean_object* v_buckets_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_size_244_ = lean_ctor_get(v_m_243_, 0);
v_buckets_245_ = lean_ctor_get(v_m_243_, 1);
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_nat_mul(v_size_244_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(3u);
v___x_249_ = lean_nat_div(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_array_get_size(v_buckets_245_);
v___x_251_ = lean_nat_dec_le(v___x_249_, v___x_250_);
lean_dec(v___x_249_);
if (v___x_251_ == 0)
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
lean_inc_ref(v_buckets_245_);
lean_inc(v_size_244_);
v_isSharedCheck_259_ = !lean_is_exclusive(v_m_243_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; lean_object* v_unused_261_; 
v_unused_260_ = lean_ctor_get(v_m_243_, 1);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_m_243_, 0);
lean_dec(v_unused_261_);
v___x_253_ = v_m_243_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_m_243_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_val_255_; lean_object* v___x_257_; 
v_val_255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_242_, v_buckets_245_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v_val_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_size_244_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_val_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_dec_ref(v_inst_242_);
return v_m_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___boxed(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_m_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(v_00_u03b1_262_, v_00_u03b2_263_, v_inst_264_, v_inst_265_, v_m_266_);
lean_dec_ref(v_inst_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_m_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_size_273_; lean_object* v_buckets_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_319_; 
v_size_273_ = lean_ctor_get(v_m_270_, 0);
v_buckets_274_ = lean_ctor_get(v_m_270_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_m_270_);
if (v_isSharedCheck_319_ == 0)
{
v___x_276_ = v_m_270_;
v_isShared_277_ = v_isSharedCheck_319_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_buckets_274_);
lean_inc(v_size_273_);
lean_dec(v_m_270_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_319_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v_fold_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v_bkt_293_; uint8_t v___x_294_; 
v___x_278_ = lean_array_get_size(v_buckets_274_);
lean_inc_ref(v_inst_269_);
lean_inc_n(v_a_271_, 2);
v___x_279_ = lean_apply_1(v_inst_269_, v_a_271_);
v___x_280_ = 32ULL;
v___x_281_ = lean_unbox_uint64(v___x_279_);
v___x_282_ = lean_uint64_shift_right(v___x_281_, v___x_280_);
v___x_283_ = lean_unbox_uint64(v___x_279_);
lean_dec_ref(v___x_279_);
v_fold_284_ = lean_uint64_xor(v___x_283_, v___x_282_);
v___x_285_ = 16ULL;
v___x_286_ = lean_uint64_shift_right(v_fold_284_, v___x_285_);
v___x_287_ = lean_uint64_xor(v_fold_284_, v___x_286_);
v___x_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = lean_usize_of_nat(v___x_278_);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_sub(v___x_289_, v___x_290_);
v___x_292_ = lean_usize_land(v___x_288_, v___x_291_);
v_bkt_293_ = lean_array_uget_borrowed(v_buckets_274_, v___x_292_);
lean_inc(v_bkt_293_);
lean_inc_ref(v_inst_268_);
v___x_294_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_268_, v_a_271_, v_bkt_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v_size_x27_296_; lean_object* v___x_297_; lean_object* v_buckets_x27_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
lean_dec_ref(v_inst_268_);
v___x_295_ = lean_unsigned_to_nat(1u);
v_size_x27_296_ = lean_nat_add(v_size_273_, v___x_295_);
lean_dec(v_size_273_);
lean_inc(v_bkt_293_);
v___x_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_297_, 0, v_a_271_);
lean_ctor_set(v___x_297_, 1, v_b_272_);
lean_ctor_set(v___x_297_, 2, v_bkt_293_);
v_buckets_x27_298_ = lean_array_uset(v_buckets_274_, v___x_292_, v___x_297_);
v___x_299_ = lean_unsigned_to_nat(4u);
v___x_300_ = lean_nat_mul(v_size_x27_296_, v___x_299_);
v___x_301_ = lean_unsigned_to_nat(3u);
v___x_302_ = lean_nat_div(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_array_get_size(v_buckets_x27_298_);
v___x_304_ = lean_nat_dec_le(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
if (v___x_304_ == 0)
{
lean_object* v_val_305_; lean_object* v___x_307_; 
v_val_305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_269_, v_buckets_x27_298_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v_val_305_);
lean_ctor_set(v___x_276_, 0, v_size_x27_296_);
v___x_307_ = v___x_276_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_size_x27_296_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_val_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
lean_object* v___x_310_; 
lean_dec_ref(v_inst_269_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v_buckets_x27_298_);
lean_ctor_set(v___x_276_, 0, v_size_x27_296_);
v___x_310_ = v___x_276_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_size_x27_296_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_buckets_x27_298_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v___x_312_; lean_object* v_buckets_x27_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
lean_inc(v_bkt_293_);
lean_dec_ref(v_inst_269_);
v___x_312_ = lean_box(0);
v_buckets_x27_313_ = lean_array_uset(v_buckets_274_, v___x_292_, v___x_312_);
v___x_314_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_268_, v_a_271_, v_b_272_, v_bkt_293_);
v___x_315_ = lean_array_uset(v_buckets_x27_313_, v___x_292_, v___x_314_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_315_);
v___x_317_ = v___x_276_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_size_273_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_m_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_322_, v_inst_323_, v_m_324_, v_a_325_, v_b_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_m_330_, lean_object* v_a_331_, lean_object* v_f_332_){
_start:
{
lean_object* v_size_333_; lean_object* v_buckets_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v_fold_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_bucket_350_; uint8_t v___x_351_; 
v_size_333_ = lean_ctor_get(v_m_330_, 0);
v_buckets_334_ = lean_ctor_get(v_m_330_, 1);
v___x_335_ = lean_array_get_size(v_buckets_334_);
lean_inc_n(v_a_331_, 2);
v___x_336_ = lean_apply_1(v_inst_329_, v_a_331_);
v___x_337_ = 32ULL;
v___x_338_ = lean_unbox_uint64(v___x_336_);
v___x_339_ = lean_uint64_shift_right(v___x_338_, v___x_337_);
v___x_340_ = lean_unbox_uint64(v___x_336_);
lean_dec_ref(v___x_336_);
v_fold_341_ = lean_uint64_xor(v___x_340_, v___x_339_);
v___x_342_ = 16ULL;
v___x_343_ = lean_uint64_shift_right(v_fold_341_, v___x_342_);
v___x_344_ = lean_uint64_xor(v_fold_341_, v___x_343_);
v___x_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = lean_usize_of_nat(v___x_335_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_land(v___x_345_, v___x_348_);
v_bucket_350_ = lean_array_uget_borrowed(v_buckets_334_, v___x_349_);
lean_inc(v_bucket_350_);
lean_inc_ref(v_inst_328_);
v___x_351_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_328_, v_a_331_, v_bucket_350_);
if (v___x_351_ == 0)
{
lean_dec(v_f_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_inst_328_);
return v_m_330_;
}
else
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_362_; 
lean_inc(v_bucket_350_);
lean_inc_ref(v_buckets_334_);
lean_inc(v_size_333_);
v_isSharedCheck_362_ = !lean_is_exclusive(v_m_330_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_363_ = lean_ctor_get(v_m_330_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_m_330_, 0);
lean_dec(v_unused_364_);
v___x_353_ = v_m_330_;
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
else
{
lean_dec(v_m_330_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v_buckets_356_; lean_object* v_bucket_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_355_ = lean_box(0);
v_buckets_356_ = lean_array_uset(v_buckets_334_, v___x_349_, v___x_355_);
v_bucket_357_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(v_inst_328_, v_a_331_, v_f_332_, v_bucket_350_);
v___x_358_ = lean_array_uset(v_buckets_356_, v___x_349_, v_bucket_357_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_358_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_size_333_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify(lean_object* v_00_u03b1_365_, lean_object* v_00_u03b2_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_m_370_, lean_object* v_a_371_, lean_object* v_f_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_367_, v_inst_368_, v_m_370_, v_a_371_, v_f_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_m_376_, lean_object* v_a_377_, lean_object* v_f_378_){
_start:
{
lean_object* v_size_379_; lean_object* v_buckets_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint64_t v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v_fold_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; lean_object* v_bucket_396_; uint8_t v___x_397_; 
v_size_379_ = lean_ctor_get(v_m_376_, 0);
v_buckets_380_ = lean_ctor_get(v_m_376_, 1);
v___x_381_ = lean_array_get_size(v_buckets_380_);
lean_inc_n(v_a_377_, 2);
v___x_382_ = lean_apply_1(v_inst_375_, v_a_377_);
v___x_383_ = 32ULL;
v___x_384_ = lean_unbox_uint64(v___x_382_);
v___x_385_ = lean_uint64_shift_right(v___x_384_, v___x_383_);
v___x_386_ = lean_unbox_uint64(v___x_382_);
lean_dec_ref(v___x_382_);
v_fold_387_ = lean_uint64_xor(v___x_386_, v___x_385_);
v___x_388_ = 16ULL;
v___x_389_ = lean_uint64_shift_right(v_fold_387_, v___x_388_);
v___x_390_ = lean_uint64_xor(v_fold_387_, v___x_389_);
v___x_391_ = lean_uint64_to_usize(v___x_390_);
v___x_392_ = lean_usize_of_nat(v___x_381_);
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_sub(v___x_392_, v___x_393_);
v___x_395_ = lean_usize_land(v___x_391_, v___x_394_);
v_bucket_396_ = lean_array_uget_borrowed(v_buckets_380_, v___x_395_);
lean_inc(v_bucket_396_);
lean_inc_ref(v_inst_374_);
v___x_397_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_374_, v_a_377_, v_bucket_396_);
if (v___x_397_ == 0)
{
lean_dec(v_f_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_inst_374_);
return v_m_376_;
}
else
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_408_; 
lean_inc(v_bucket_396_);
lean_inc_ref(v_buckets_380_);
lean_inc(v_size_379_);
v_isSharedCheck_408_ = !lean_is_exclusive(v_m_376_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; lean_object* v_unused_410_; 
v_unused_409_ = lean_ctor_get(v_m_376_, 1);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_m_376_, 0);
lean_dec(v_unused_410_);
v___x_399_ = v_m_376_;
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_m_376_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v_buckets_402_; lean_object* v_bucket_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_401_ = lean_box(0);
v_buckets_402_ = lean_array_uset(v_buckets_380_, v___x_395_, v___x_401_);
v_bucket_403_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(v_inst_374_, v_a_377_, v_f_378_, v_bucket_396_);
v___x_404_ = lean_array_uset(v_buckets_402_, v___x_395_, v_bucket_403_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_404_);
v___x_406_ = v___x_399_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_size_379_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify(lean_object* v_00_u03b1_411_, lean_object* v_inst_412_, lean_object* v_00_u03b2_413_, lean_object* v_inst_414_, lean_object* v_m_415_, lean_object* v_a_416_, lean_object* v_f_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_412_, v_inst_414_, v_m_415_, v_a_416_, v_f_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_m_421_, lean_object* v_a_422_, lean_object* v_f_423_){
_start:
{
lean_object* v_size_424_; lean_object* v_buckets_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint64_t v___x_428_; uint64_t v___x_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v_fold_432_; uint64_t v___x_433_; uint64_t v___x_434_; uint64_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v_bkt_441_; uint8_t v___x_442_; 
v_size_424_ = lean_ctor_get(v_m_421_, 0);
v_buckets_425_ = lean_ctor_get(v_m_421_, 1);
v___x_426_ = lean_array_get_size(v_buckets_425_);
lean_inc_ref(v_inst_420_);
lean_inc_n(v_a_422_, 2);
v___x_427_ = lean_apply_1(v_inst_420_, v_a_422_);
v___x_428_ = 32ULL;
v___x_429_ = lean_unbox_uint64(v___x_427_);
v___x_430_ = lean_uint64_shift_right(v___x_429_, v___x_428_);
v___x_431_ = lean_unbox_uint64(v___x_427_);
lean_dec_ref(v___x_427_);
v_fold_432_ = lean_uint64_xor(v___x_431_, v___x_430_);
v___x_433_ = 16ULL;
v___x_434_ = lean_uint64_shift_right(v_fold_432_, v___x_433_);
v___x_435_ = lean_uint64_xor(v_fold_432_, v___x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = lean_usize_of_nat(v___x_426_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_sub(v___x_437_, v___x_438_);
v___x_440_ = lean_usize_land(v___x_436_, v___x_439_);
v_bkt_441_ = lean_array_uget_borrowed(v_buckets_425_, v___x_440_);
lean_inc(v_bkt_441_);
lean_inc_ref(v_inst_419_);
v___x_442_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_419_, v_a_422_, v_bkt_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec_ref(v_inst_419_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_apply_1(v_f_423_, v___x_443_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_dec(v_a_422_);
lean_dec_ref(v_inst_420_);
return v_m_421_;
}
else
{
lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_466_; 
lean_inc_ref(v_buckets_425_);
lean_inc(v_size_424_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_m_421_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; lean_object* v_unused_468_; 
v_unused_467_ = lean_ctor_get(v_m_421_, 1);
lean_dec(v_unused_467_);
v_unused_468_ = lean_ctor_get(v_m_421_, 0);
lean_dec(v_unused_468_);
v___x_446_ = v_m_421_;
v_isShared_447_ = v_isSharedCheck_466_;
goto v_resetjp_445_;
}
else
{
lean_dec(v_m_421_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_466_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v_val_448_; lean_object* v___x_449_; lean_object* v_size_x27_450_; lean_object* v___x_451_; lean_object* v_buckets_x27_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_val_448_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v___x_444_, 1);
v___x_449_ = lean_unsigned_to_nat(1u);
v_size_x27_450_ = lean_nat_add(v_size_424_, v___x_449_);
lean_dec(v_size_424_);
lean_inc(v_bkt_441_);
v___x_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_451_, 0, v_a_422_);
lean_ctor_set(v___x_451_, 1, v_val_448_);
lean_ctor_set(v___x_451_, 2, v_bkt_441_);
v_buckets_x27_452_ = lean_array_uset(v_buckets_425_, v___x_440_, v___x_451_);
v___x_453_ = lean_unsigned_to_nat(4u);
v___x_454_ = lean_nat_mul(v_size_x27_450_, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(3u);
v___x_456_ = lean_nat_div(v___x_454_, v___x_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_array_get_size(v_buckets_x27_452_);
v___x_458_ = lean_nat_dec_le(v___x_456_, v___x_457_);
lean_dec(v___x_456_);
if (v___x_458_ == 0)
{
lean_object* v_val_459_; lean_object* v___x_461_; 
v_val_459_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_420_, v_buckets_x27_452_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_val_459_);
lean_ctor_set(v___x_446_, 0, v_size_x27_450_);
v___x_461_ = v___x_446_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_size_x27_450_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_val_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec_ref(v_inst_420_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_buckets_x27_452_);
lean_ctor_set(v___x_446_, 0, v_size_x27_450_);
v___x_464_ = v___x_446_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_size_x27_450_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_buckets_x27_452_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
else
{
lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_484_; 
lean_inc(v_bkt_441_);
lean_inc_ref(v_buckets_425_);
lean_inc(v_size_424_);
lean_dec_ref(v_inst_420_);
v_isSharedCheck_484_ = !lean_is_exclusive(v_m_421_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; lean_object* v_unused_486_; 
v_unused_485_ = lean_ctor_get(v_m_421_, 1);
lean_dec(v_unused_485_);
v_unused_486_ = lean_ctor_get(v_m_421_, 0);
lean_dec(v_unused_486_);
v___x_470_ = v_m_421_;
v_isShared_471_ = v_isSharedCheck_484_;
goto v_resetjp_469_;
}
else
{
lean_dec(v_m_421_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_484_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v_buckets_x27_473_; lean_object* v_bkt_x27_474_; lean_object* v___y_476_; uint8_t v___x_481_; 
v___x_472_ = lean_box(0);
v_buckets_x27_473_ = lean_array_uset(v_buckets_425_, v___x_440_, v___x_472_);
lean_inc(v_a_422_);
lean_inc_ref(v_inst_419_);
v_bkt_x27_474_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(v_inst_419_, v_a_422_, v_f_423_, v_bkt_441_);
lean_inc(v_bkt_x27_474_);
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_419_, v_a_422_, v_bkt_x27_474_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_sub(v_size_424_, v___x_482_);
lean_dec(v_size_424_);
v___y_476_ = v___x_483_;
goto v___jp_475_;
}
else
{
v___y_476_ = v_size_424_;
goto v___jp_475_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = lean_array_uset(v_buckets_x27_473_, v___x_440_, v_bkt_x27_474_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v___x_477_);
lean_ctor_set(v___x_470_, 0, v___y_476_);
v___x_479_ = v___x_470_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___y_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter(lean_object* v_00_u03b1_487_, lean_object* v_00_u03b2_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_m_492_, lean_object* v_a_493_, lean_object* v_f_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_489_, v_inst_490_, v_m_492_, v_a_493_, v_f_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_f_500_){
_start:
{
lean_object* v_size_501_; lean_object* v_buckets_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint64_t v___x_505_; uint64_t v___x_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v_fold_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v_bkt_518_; uint8_t v___x_519_; 
v_size_501_ = lean_ctor_get(v_m_498_, 0);
v_buckets_502_ = lean_ctor_get(v_m_498_, 1);
v___x_503_ = lean_array_get_size(v_buckets_502_);
lean_inc_ref(v_inst_497_);
lean_inc_n(v_a_499_, 2);
v___x_504_ = lean_apply_1(v_inst_497_, v_a_499_);
v___x_505_ = 32ULL;
v___x_506_ = lean_unbox_uint64(v___x_504_);
v___x_507_ = lean_uint64_shift_right(v___x_506_, v___x_505_);
v___x_508_ = lean_unbox_uint64(v___x_504_);
lean_dec_ref(v___x_504_);
v_fold_509_ = lean_uint64_xor(v___x_508_, v___x_507_);
v___x_510_ = 16ULL;
v___x_511_ = lean_uint64_shift_right(v_fold_509_, v___x_510_);
v___x_512_ = lean_uint64_xor(v_fold_509_, v___x_511_);
v___x_513_ = lean_uint64_to_usize(v___x_512_);
v___x_514_ = lean_usize_of_nat(v___x_503_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_sub(v___x_514_, v___x_515_);
v___x_517_ = lean_usize_land(v___x_513_, v___x_516_);
v_bkt_518_ = lean_array_uget_borrowed(v_buckets_502_, v___x_517_);
lean_inc(v_bkt_518_);
lean_inc_ref(v_inst_496_);
v___x_519_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_496_, v_a_499_, v_bkt_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref(v_inst_496_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_f_500_, v___x_520_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_dec(v_a_499_);
lean_dec_ref(v_inst_497_);
return v_m_498_;
}
else
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_543_; 
lean_inc_ref(v_buckets_502_);
lean_inc(v_size_501_);
v_isSharedCheck_543_ = !lean_is_exclusive(v_m_498_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; lean_object* v_unused_545_; 
v_unused_544_ = lean_ctor_get(v_m_498_, 1);
lean_dec(v_unused_544_);
v_unused_545_ = lean_ctor_get(v_m_498_, 0);
lean_dec(v_unused_545_);
v___x_523_ = v_m_498_;
v_isShared_524_ = v_isSharedCheck_543_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_m_498_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_543_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_val_525_; lean_object* v___x_526_; lean_object* v_size_x27_527_; lean_object* v___x_528_; lean_object* v_buckets_x27_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_val_525_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v___x_521_, 1);
v___x_526_ = lean_unsigned_to_nat(1u);
v_size_x27_527_ = lean_nat_add(v_size_501_, v___x_526_);
lean_dec(v_size_501_);
lean_inc(v_bkt_518_);
v___x_528_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_528_, 0, v_a_499_);
lean_ctor_set(v___x_528_, 1, v_val_525_);
lean_ctor_set(v___x_528_, 2, v_bkt_518_);
v_buckets_x27_529_ = lean_array_uset(v_buckets_502_, v___x_517_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(4u);
v___x_531_ = lean_nat_mul(v_size_x27_527_, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(3u);
v___x_533_ = lean_nat_div(v___x_531_, v___x_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_array_get_size(v_buckets_x27_529_);
v___x_535_ = lean_nat_dec_le(v___x_533_, v___x_534_);
lean_dec(v___x_533_);
if (v___x_535_ == 0)
{
lean_object* v_val_536_; lean_object* v___x_538_; 
v_val_536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_497_, v_buckets_x27_529_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_val_536_);
lean_ctor_set(v___x_523_, 0, v_size_x27_527_);
v___x_538_ = v___x_523_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_size_x27_527_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_val_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
else
{
lean_object* v___x_541_; 
lean_dec_ref(v_inst_497_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_buckets_x27_529_);
lean_ctor_set(v___x_523_, 0, v_size_x27_527_);
v___x_541_ = v___x_523_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_size_x27_527_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_buckets_x27_529_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
else
{
lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_561_; 
lean_inc(v_bkt_518_);
lean_inc_ref(v_buckets_502_);
lean_inc(v_size_501_);
lean_dec_ref(v_inst_497_);
v_isSharedCheck_561_ = !lean_is_exclusive(v_m_498_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; lean_object* v_unused_563_; 
v_unused_562_ = lean_ctor_get(v_m_498_, 1);
lean_dec(v_unused_562_);
v_unused_563_ = lean_ctor_get(v_m_498_, 0);
lean_dec(v_unused_563_);
v___x_547_ = v_m_498_;
v_isShared_548_ = v_isSharedCheck_561_;
goto v_resetjp_546_;
}
else
{
lean_dec(v_m_498_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_561_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v_buckets_x27_550_; lean_object* v_bkt_x27_551_; lean_object* v___y_553_; uint8_t v___x_558_; 
v___x_549_ = lean_box(0);
v_buckets_x27_550_ = lean_array_uset(v_buckets_502_, v___x_517_, v___x_549_);
lean_inc(v_a_499_);
lean_inc_ref(v_inst_496_);
v_bkt_x27_551_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(v_inst_496_, v_a_499_, v_f_500_, v_bkt_518_);
lean_inc(v_bkt_x27_551_);
v___x_558_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_496_, v_a_499_, v_bkt_x27_551_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_sub(v_size_501_, v___x_559_);
lean_dec(v_size_501_);
v___y_553_ = v___x_560_;
goto v___jp_552_;
}
else
{
v___y_553_ = v_size_501_;
goto v___jp_552_;
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_array_uset(v_buckets_x27_550_, v___x_517_, v_bkt_x27_551_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 1, v___x_554_);
lean_ctor_set(v___x_547_, 0, v___y_553_);
v___x_556_ = v___x_547_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___y_553_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter(lean_object* v_00_u03b1_564_, lean_object* v_inst_565_, lean_object* v_inst_566_, lean_object* v_00_u03b2_567_, lean_object* v_m_568_, lean_object* v_a_569_, lean_object* v_f_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_565_, v_inst_566_, v_m_568_, v_a_569_, v_f_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert___redArg(lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_m_574_, lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
lean_object* v_size_577_; lean_object* v_buckets_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_629_; 
v_size_577_ = lean_ctor_get(v_m_574_, 0);
v_buckets_578_ = lean_ctor_get(v_m_574_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_m_574_);
if (v_isSharedCheck_629_ == 0)
{
v___x_580_ = v_m_574_;
v_isShared_581_ = v_isSharedCheck_629_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_buckets_578_);
lean_inc(v_size_577_);
lean_dec(v_m_574_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_629_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; uint64_t v___x_584_; uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; uint64_t v_fold_588_; uint64_t v___x_589_; uint64_t v___x_590_; uint64_t v___x_591_; size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v_bkt_597_; uint8_t v___x_598_; 
v___x_582_ = lean_array_get_size(v_buckets_578_);
lean_inc_ref(v_inst_573_);
lean_inc_n(v_a_575_, 2);
v___x_583_ = lean_apply_1(v_inst_573_, v_a_575_);
v___x_584_ = 32ULL;
v___x_585_ = lean_unbox_uint64(v___x_583_);
v___x_586_ = lean_uint64_shift_right(v___x_585_, v___x_584_);
v___x_587_ = lean_unbox_uint64(v___x_583_);
lean_dec_ref(v___x_583_);
v_fold_588_ = lean_uint64_xor(v___x_587_, v___x_586_);
v___x_589_ = 16ULL;
v___x_590_ = lean_uint64_shift_right(v_fold_588_, v___x_589_);
v___x_591_ = lean_uint64_xor(v_fold_588_, v___x_590_);
v___x_592_ = lean_uint64_to_usize(v___x_591_);
v___x_593_ = lean_usize_of_nat(v___x_582_);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_sub(v___x_593_, v___x_594_);
v___x_596_ = lean_usize_land(v___x_592_, v___x_595_);
v_bkt_597_ = lean_array_uget_borrowed(v_buckets_578_, v___x_596_);
lean_inc(v_bkt_597_);
lean_inc_ref(v_inst_572_);
v___x_598_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_572_, v_a_575_, v_bkt_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v_size_x27_600_; lean_object* v___x_601_; lean_object* v_buckets_x27_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
lean_dec_ref(v_inst_572_);
v___x_599_ = lean_unsigned_to_nat(1u);
v_size_x27_600_ = lean_nat_add(v_size_577_, v___x_599_);
lean_dec(v_size_577_);
lean_inc(v_bkt_597_);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v_a_575_);
lean_ctor_set(v___x_601_, 1, v_b_576_);
lean_ctor_set(v___x_601_, 2, v_bkt_597_);
v_buckets_x27_602_ = lean_array_uset(v_buckets_578_, v___x_596_, v___x_601_);
v___x_603_ = lean_unsigned_to_nat(4u);
v___x_604_ = lean_nat_mul(v_size_x27_600_, v___x_603_);
v___x_605_ = lean_unsigned_to_nat(3u);
v___x_606_ = lean_nat_div(v___x_604_, v___x_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_array_get_size(v_buckets_x27_602_);
v___x_608_ = lean_nat_dec_le(v___x_606_, v___x_607_);
lean_dec(v___x_606_);
if (v___x_608_ == 0)
{
lean_object* v_val_609_; lean_object* v___x_611_; 
v_val_609_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_573_, v_buckets_x27_602_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_val_609_);
lean_ctor_set(v___x_580_, 0, v_size_x27_600_);
v___x_611_ = v___x_580_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_size_x27_600_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_val_609_);
v___x_611_ = v_reuseFailAlloc_614_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_box(v___x_598_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
return v___x_613_;
}
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v_inst_573_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_buckets_x27_602_);
lean_ctor_set(v___x_580_, 0, v_size_x27_600_);
v___x_616_ = v___x_580_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_size_x27_600_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_buckets_x27_602_);
v___x_616_ = v_reuseFailAlloc_619_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_box(v___x_598_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_616_);
return v___x_618_;
}
}
}
else
{
lean_object* v___x_620_; lean_object* v_buckets_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
lean_inc(v_bkt_597_);
lean_dec_ref(v_inst_573_);
v___x_620_ = lean_box(0);
v_buckets_x27_621_ = lean_array_uset(v_buckets_578_, v___x_596_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_572_, v_a_575_, v_b_576_, v_bkt_597_);
v___x_623_ = lean_array_uset(v_buckets_x27_621_, v___x_596_, v___x_622_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_623_);
v___x_625_ = v___x_580_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_size_577_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_628_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(v___x_598_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
return v___x_627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_m_634_, lean_object* v_a_635_, lean_object* v_b_636_){
_start:
{
lean_object* v_size_637_; lean_object* v_buckets_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_689_; 
v_size_637_ = lean_ctor_get(v_m_634_, 0);
v_buckets_638_ = lean_ctor_get(v_m_634_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_m_634_);
if (v_isSharedCheck_689_ == 0)
{
v___x_640_ = v_m_634_;
v_isShared_641_ = v_isSharedCheck_689_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_buckets_638_);
lean_inc(v_size_637_);
lean_dec(v_m_634_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_689_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; uint64_t v_fold_648_; uint64_t v___x_649_; uint64_t v___x_650_; uint64_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; lean_object* v_bkt_657_; uint8_t v___x_658_; 
v___x_642_ = lean_array_get_size(v_buckets_638_);
lean_inc_ref(v_inst_633_);
lean_inc_n(v_a_635_, 2);
v___x_643_ = lean_apply_1(v_inst_633_, v_a_635_);
v___x_644_ = 32ULL;
v___x_645_ = lean_unbox_uint64(v___x_643_);
v___x_646_ = lean_uint64_shift_right(v___x_645_, v___x_644_);
v___x_647_ = lean_unbox_uint64(v___x_643_);
lean_dec_ref(v___x_643_);
v_fold_648_ = lean_uint64_xor(v___x_647_, v___x_646_);
v___x_649_ = 16ULL;
v___x_650_ = lean_uint64_shift_right(v_fold_648_, v___x_649_);
v___x_651_ = lean_uint64_xor(v_fold_648_, v___x_650_);
v___x_652_ = lean_uint64_to_usize(v___x_651_);
v___x_653_ = lean_usize_of_nat(v___x_642_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_sub(v___x_653_, v___x_654_);
v___x_656_ = lean_usize_land(v___x_652_, v___x_655_);
v_bkt_657_ = lean_array_uget_borrowed(v_buckets_638_, v___x_656_);
lean_inc(v_bkt_657_);
lean_inc_ref(v_inst_632_);
v___x_658_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_632_, v_a_635_, v_bkt_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v_size_x27_660_; lean_object* v___x_661_; lean_object* v_buckets_x27_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
lean_dec_ref(v_inst_632_);
v___x_659_ = lean_unsigned_to_nat(1u);
v_size_x27_660_ = lean_nat_add(v_size_637_, v___x_659_);
lean_dec(v_size_637_);
lean_inc(v_bkt_657_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v_a_635_);
lean_ctor_set(v___x_661_, 1, v_b_636_);
lean_ctor_set(v___x_661_, 2, v_bkt_657_);
v_buckets_x27_662_ = lean_array_uset(v_buckets_638_, v___x_656_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_mul(v_size_x27_660_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(3u);
v___x_666_ = lean_nat_div(v___x_664_, v___x_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_array_get_size(v_buckets_x27_662_);
v___x_668_ = lean_nat_dec_le(v___x_666_, v___x_667_);
lean_dec(v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v_val_669_; lean_object* v___x_671_; 
v_val_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_633_, v_buckets_x27_662_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_val_669_);
lean_ctor_set(v___x_640_, 0, v_size_x27_660_);
v___x_671_ = v___x_640_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_size_x27_660_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_val_669_);
v___x_671_ = v_reuseFailAlloc_674_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(v___x_658_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
return v___x_673_;
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v_inst_633_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_buckets_x27_662_);
lean_ctor_set(v___x_640_, 0, v_size_x27_660_);
v___x_676_ = v___x_640_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_size_x27_660_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_buckets_x27_662_);
v___x_676_ = v_reuseFailAlloc_679_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_box(v___x_658_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
return v___x_678_;
}
}
}
else
{
lean_object* v___x_680_; lean_object* v_buckets_x27_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
lean_inc(v_bkt_657_);
lean_dec_ref(v_inst_633_);
v___x_680_ = lean_box(0);
v_buckets_x27_681_ = lean_array_uset(v_buckets_638_, v___x_656_, v___x_680_);
v___x_682_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_632_, v_a_635_, v_b_636_, v_bkt_657_);
v___x_683_ = lean_array_uset(v_buckets_x27_681_, v___x_656_, v___x_682_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_683_);
v___x_685_ = v___x_640_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_size_637_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_688_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_box(v___x_658_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew___redArg(lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_m_692_, lean_object* v_a_693_, lean_object* v_b_694_){
_start:
{
lean_object* v_size_695_; lean_object* v_buckets_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v_fold_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v_bkt_712_; uint8_t v___x_713_; 
v_size_695_ = lean_ctor_get(v_m_692_, 0);
v_buckets_696_ = lean_ctor_get(v_m_692_, 1);
v___x_697_ = lean_array_get_size(v_buckets_696_);
lean_inc_ref(v_inst_691_);
lean_inc_n(v_a_693_, 2);
v___x_698_ = lean_apply_1(v_inst_691_, v_a_693_);
v___x_699_ = 32ULL;
v___x_700_ = lean_unbox_uint64(v___x_698_);
v___x_701_ = lean_uint64_shift_right(v___x_700_, v___x_699_);
v___x_702_ = lean_unbox_uint64(v___x_698_);
lean_dec_ref(v___x_698_);
v_fold_703_ = lean_uint64_xor(v___x_702_, v___x_701_);
v___x_704_ = 16ULL;
v___x_705_ = lean_uint64_shift_right(v_fold_703_, v___x_704_);
v___x_706_ = lean_uint64_xor(v_fold_703_, v___x_705_);
v___x_707_ = lean_uint64_to_usize(v___x_706_);
v___x_708_ = lean_usize_of_nat(v___x_697_);
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_sub(v___x_708_, v___x_709_);
v___x_711_ = lean_usize_land(v___x_707_, v___x_710_);
v_bkt_712_ = lean_array_uget_borrowed(v_buckets_696_, v___x_711_);
lean_inc(v_bkt_712_);
v___x_713_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_690_, v_a_693_, v_bkt_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_738_; 
lean_inc_ref(v_buckets_696_);
lean_inc(v_size_695_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_m_692_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; lean_object* v_unused_740_; 
v_unused_739_ = lean_ctor_get(v_m_692_, 1);
lean_dec(v_unused_739_);
v_unused_740_ = lean_ctor_get(v_m_692_, 0);
lean_dec(v_unused_740_);
v___x_715_ = v_m_692_;
v_isShared_716_ = v_isSharedCheck_738_;
goto v_resetjp_714_;
}
else
{
lean_dec(v_m_692_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_738_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v_size_x27_718_; lean_object* v___x_719_; lean_object* v_buckets_x27_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v_size_x27_718_ = lean_nat_add(v_size_695_, v___x_717_);
lean_dec(v_size_695_);
lean_inc(v_bkt_712_);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v_a_693_);
lean_ctor_set(v___x_719_, 1, v_b_694_);
lean_ctor_set(v___x_719_, 2, v_bkt_712_);
v_buckets_x27_720_ = lean_array_uset(v_buckets_696_, v___x_711_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_mul(v_size_x27_718_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = lean_nat_div(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_array_get_size(v_buckets_x27_720_);
v___x_726_ = lean_nat_dec_le(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v_val_727_; lean_object* v___x_729_; 
v_val_727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_691_, v_buckets_x27_720_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_val_727_);
lean_ctor_set(v___x_715_, 0, v_size_x27_718_);
v___x_729_ = v___x_715_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_size_x27_718_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_val_727_);
v___x_729_ = v_reuseFailAlloc_732_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_box(v___x_713_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v___x_729_);
return v___x_731_;
}
}
else
{
lean_object* v___x_734_; 
lean_dec_ref(v_inst_691_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_buckets_x27_720_);
lean_ctor_set(v___x_715_, 0, v_size_x27_718_);
v___x_734_ = v___x_715_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_size_x27_718_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_buckets_x27_720_);
v___x_734_ = v_reuseFailAlloc_737_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(v___x_713_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
return v___x_736_;
}
}
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_b_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_inst_691_);
v___x_741_ = lean_box(v___x_713_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_m_692_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_m_747_, lean_object* v_a_748_, lean_object* v_b_749_){
_start:
{
lean_object* v_size_750_; lean_object* v_buckets_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint64_t v___x_754_; uint64_t v___x_755_; uint64_t v___x_756_; uint64_t v___x_757_; uint64_t v_fold_758_; uint64_t v___x_759_; uint64_t v___x_760_; uint64_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v_bkt_767_; uint8_t v___x_768_; 
v_size_750_ = lean_ctor_get(v_m_747_, 0);
v_buckets_751_ = lean_ctor_get(v_m_747_, 1);
v___x_752_ = lean_array_get_size(v_buckets_751_);
lean_inc_ref(v_inst_746_);
lean_inc_n(v_a_748_, 2);
v___x_753_ = lean_apply_1(v_inst_746_, v_a_748_);
v___x_754_ = 32ULL;
v___x_755_ = lean_unbox_uint64(v___x_753_);
v___x_756_ = lean_uint64_shift_right(v___x_755_, v___x_754_);
v___x_757_ = lean_unbox_uint64(v___x_753_);
lean_dec_ref(v___x_753_);
v_fold_758_ = lean_uint64_xor(v___x_757_, v___x_756_);
v___x_759_ = 16ULL;
v___x_760_ = lean_uint64_shift_right(v_fold_758_, v___x_759_);
v___x_761_ = lean_uint64_xor(v_fold_758_, v___x_760_);
v___x_762_ = lean_uint64_to_usize(v___x_761_);
v___x_763_ = lean_usize_of_nat(v___x_752_);
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_sub(v___x_763_, v___x_764_);
v___x_766_ = lean_usize_land(v___x_762_, v___x_765_);
v_bkt_767_ = lean_array_uget_borrowed(v_buckets_751_, v___x_766_);
lean_inc(v_bkt_767_);
v___x_768_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_745_, v_a_748_, v_bkt_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_793_; 
lean_inc_ref(v_buckets_751_);
lean_inc(v_size_750_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_m_747_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_794_ = lean_ctor_get(v_m_747_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_m_747_, 0);
lean_dec(v_unused_795_);
v___x_770_ = v_m_747_;
v_isShared_771_ = v_isSharedCheck_793_;
goto v_resetjp_769_;
}
else
{
lean_dec(v_m_747_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_793_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v_size_x27_773_; lean_object* v___x_774_; lean_object* v_buckets_x27_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v_size_x27_773_ = lean_nat_add(v_size_750_, v___x_772_);
lean_dec(v_size_750_);
lean_inc(v_bkt_767_);
v___x_774_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_774_, 0, v_a_748_);
lean_ctor_set(v___x_774_, 1, v_b_749_);
lean_ctor_set(v___x_774_, 2, v_bkt_767_);
v_buckets_x27_775_ = lean_array_uset(v_buckets_751_, v___x_766_, v___x_774_);
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = lean_nat_mul(v_size_x27_773_, v___x_776_);
v___x_778_ = lean_unsigned_to_nat(3u);
v___x_779_ = lean_nat_div(v___x_777_, v___x_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_array_get_size(v_buckets_x27_775_);
v___x_781_ = lean_nat_dec_le(v___x_779_, v___x_780_);
lean_dec(v___x_779_);
if (v___x_781_ == 0)
{
lean_object* v_val_782_; lean_object* v___x_784_; 
v_val_782_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_746_, v_buckets_x27_775_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_val_782_);
lean_ctor_set(v___x_770_, 0, v_size_x27_773_);
v___x_784_ = v___x_770_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_size_x27_773_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_val_782_);
v___x_784_ = v_reuseFailAlloc_787_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(v___x_768_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
return v___x_786_;
}
}
else
{
lean_object* v___x_789_; 
lean_dec_ref(v_inst_746_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_buckets_x27_775_);
lean_ctor_set(v___x_770_, 0, v_size_x27_773_);
v___x_789_ = v___x_770_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_size_x27_773_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_buckets_x27_775_);
v___x_789_ = v_reuseFailAlloc_792_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_box(v___x_768_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
return v___x_791_;
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_b_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_inst_746_);
v___x_796_ = lean_box(v___x_768_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_m_747_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_m_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_size_803_; lean_object* v_buckets_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint64_t v___x_807_; uint64_t v___x_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v_fold_811_; uint64_t v___x_812_; uint64_t v___x_813_; uint64_t v___x_814_; size_t v___x_815_; size_t v___x_816_; size_t v___x_817_; size_t v___x_818_; size_t v___x_819_; lean_object* v_bkt_820_; uint8_t v___x_821_; 
v_size_803_ = lean_ctor_get(v_m_800_, 0);
v_buckets_804_ = lean_ctor_get(v_m_800_, 1);
v___x_805_ = lean_array_get_size(v_buckets_804_);
lean_inc_ref(v_inst_799_);
lean_inc_n(v_a_801_, 2);
v___x_806_ = lean_apply_1(v_inst_799_, v_a_801_);
v___x_807_ = 32ULL;
v___x_808_ = lean_unbox_uint64(v___x_806_);
v___x_809_ = lean_uint64_shift_right(v___x_808_, v___x_807_);
v___x_810_ = lean_unbox_uint64(v___x_806_);
lean_dec_ref(v___x_806_);
v_fold_811_ = lean_uint64_xor(v___x_810_, v___x_809_);
v___x_812_ = 16ULL;
v___x_813_ = lean_uint64_shift_right(v_fold_811_, v___x_812_);
v___x_814_ = lean_uint64_xor(v_fold_811_, v___x_813_);
v___x_815_ = lean_uint64_to_usize(v___x_814_);
v___x_816_ = lean_usize_of_nat(v___x_805_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_sub(v___x_816_, v___x_817_);
v___x_819_ = lean_usize_land(v___x_815_, v___x_818_);
v_bkt_820_ = lean_array_uget_borrowed(v_buckets_804_, v___x_819_);
lean_inc(v_bkt_820_);
v___x_821_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_798_, v_a_801_, v_bkt_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_842_; 
lean_inc_ref(v_buckets_804_);
lean_inc(v_size_803_);
v_isSharedCheck_842_ = !lean_is_exclusive(v_m_800_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_843_ = lean_ctor_get(v_m_800_, 1);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_m_800_, 0);
lean_dec(v_unused_844_);
v___x_823_ = v_m_800_;
v_isShared_824_ = v_isSharedCheck_842_;
goto v_resetjp_822_;
}
else
{
lean_dec(v_m_800_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_842_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v_size_x27_826_; lean_object* v___x_827_; lean_object* v_buckets_x27_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_825_ = lean_unsigned_to_nat(1u);
v_size_x27_826_ = lean_nat_add(v_size_803_, v___x_825_);
lean_dec(v_size_803_);
lean_inc(v_bkt_820_);
v___x_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_827_, 0, v_a_801_);
lean_ctor_set(v___x_827_, 1, v_b_802_);
lean_ctor_set(v___x_827_, 2, v_bkt_820_);
v_buckets_x27_828_ = lean_array_uset(v_buckets_804_, v___x_819_, v___x_827_);
v___x_829_ = lean_unsigned_to_nat(4u);
v___x_830_ = lean_nat_mul(v_size_x27_826_, v___x_829_);
v___x_831_ = lean_unsigned_to_nat(3u);
v___x_832_ = lean_nat_div(v___x_830_, v___x_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_array_get_size(v_buckets_x27_828_);
v___x_834_ = lean_nat_dec_le(v___x_832_, v___x_833_);
lean_dec(v___x_832_);
if (v___x_834_ == 0)
{
lean_object* v_val_835_; lean_object* v___x_837_; 
v_val_835_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_799_, v_buckets_x27_828_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_val_835_);
lean_ctor_set(v___x_823_, 0, v_size_x27_826_);
v___x_837_ = v___x_823_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_size_x27_826_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_val_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v_inst_799_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_buckets_x27_828_);
lean_ctor_set(v___x_823_, 0, v_size_x27_826_);
v___x_840_ = v___x_823_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_size_x27_826_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_buckets_x27_828_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_dec(v_b_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_inst_799_);
return v_m_800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_m_849_, lean_object* v_a_850_, lean_object* v_b_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_847_, v_inst_848_, v_m_849_, v_a_850_, v_b_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_m_855_, lean_object* v_a_856_, lean_object* v_b_857_){
_start:
{
lean_object* v_size_858_; lean_object* v_buckets_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v_fold_866_; uint64_t v___x_867_; uint64_t v___x_868_; uint64_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; lean_object* v_bkt_875_; lean_object* v___x_876_; 
v_size_858_ = lean_ctor_get(v_m_855_, 0);
v_buckets_859_ = lean_ctor_get(v_m_855_, 1);
v___x_860_ = lean_array_get_size(v_buckets_859_);
lean_inc_ref(v_inst_854_);
lean_inc_n(v_a_856_, 2);
v___x_861_ = lean_apply_1(v_inst_854_, v_a_856_);
v___x_862_ = 32ULL;
v___x_863_ = lean_unbox_uint64(v___x_861_);
v___x_864_ = lean_uint64_shift_right(v___x_863_, v___x_862_);
v___x_865_ = lean_unbox_uint64(v___x_861_);
lean_dec_ref(v___x_861_);
v_fold_866_ = lean_uint64_xor(v___x_865_, v___x_864_);
v___x_867_ = 16ULL;
v___x_868_ = lean_uint64_shift_right(v_fold_866_, v___x_867_);
v___x_869_ = lean_uint64_xor(v_fold_866_, v___x_868_);
v___x_870_ = lean_uint64_to_usize(v___x_869_);
v___x_871_ = lean_usize_of_nat(v___x_860_);
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_sub(v___x_871_, v___x_872_);
v___x_874_ = lean_usize_land(v___x_870_, v___x_873_);
v_bkt_875_ = lean_array_uget_borrowed(v_buckets_859_, v___x_874_);
lean_inc(v_bkt_875_);
v___x_876_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_853_, v_a_856_, v_bkt_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_899_; 
lean_inc_ref(v_buckets_859_);
lean_inc(v_size_858_);
v_isSharedCheck_899_ = !lean_is_exclusive(v_m_855_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; lean_object* v_unused_901_; 
v_unused_900_ = lean_ctor_get(v_m_855_, 1);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_m_855_, 0);
lean_dec(v_unused_901_);
v___x_878_ = v_m_855_;
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
else
{
lean_dec(v_m_855_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_899_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v_size_x27_881_; lean_object* v___x_882_; lean_object* v_buckets_x27_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v_size_x27_881_ = lean_nat_add(v_size_858_, v___x_880_);
lean_dec(v_size_858_);
lean_inc(v_bkt_875_);
v___x_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_882_, 0, v_a_856_);
lean_ctor_set(v___x_882_, 1, v_b_857_);
lean_ctor_set(v___x_882_, 2, v_bkt_875_);
v_buckets_x27_883_ = lean_array_uset(v_buckets_859_, v___x_874_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(4u);
v___x_885_ = lean_nat_mul(v_size_x27_881_, v___x_884_);
v___x_886_ = lean_unsigned_to_nat(3u);
v___x_887_ = lean_nat_div(v___x_885_, v___x_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_array_get_size(v_buckets_x27_883_);
v___x_889_ = lean_nat_dec_le(v___x_887_, v___x_888_);
lean_dec(v___x_887_);
if (v___x_889_ == 0)
{
lean_object* v_val_890_; lean_object* v___x_892_; 
v_val_890_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_854_, v_buckets_x27_883_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v_val_890_);
lean_ctor_set(v___x_878_, 0, v_size_x27_881_);
v___x_892_ = v___x_878_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_size_x27_881_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_val_890_);
v___x_892_ = v_reuseFailAlloc_894_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_876_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
return v___x_893_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec_ref(v_inst_854_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 1, v_buckets_x27_883_);
lean_ctor_set(v___x_878_, 0, v_size_x27_881_);
v___x_896_ = v___x_878_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_size_x27_881_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_buckets_x27_883_);
v___x_896_ = v_reuseFailAlloc_898_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; 
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_876_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
return v___x_897_;
}
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec(v_b_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_inst_854_);
v___x_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_876_);
lean_ctor_set(v___x_902_, 1, v_m_855_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_903_, lean_object* v_00_u03b2_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_m_908_, lean_object* v_a_909_, lean_object* v_b_910_){
_start:
{
lean_object* v_size_911_; lean_object* v_buckets_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; uint64_t v___x_918_; uint64_t v_fold_919_; uint64_t v___x_920_; uint64_t v___x_921_; uint64_t v___x_922_; size_t v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; lean_object* v_bkt_928_; lean_object* v___x_929_; 
v_size_911_ = lean_ctor_get(v_m_908_, 0);
v_buckets_912_ = lean_ctor_get(v_m_908_, 1);
v___x_913_ = lean_array_get_size(v_buckets_912_);
lean_inc_ref(v_inst_906_);
lean_inc_n(v_a_909_, 2);
v___x_914_ = lean_apply_1(v_inst_906_, v_a_909_);
v___x_915_ = 32ULL;
v___x_916_ = lean_unbox_uint64(v___x_914_);
v___x_917_ = lean_uint64_shift_right(v___x_916_, v___x_915_);
v___x_918_ = lean_unbox_uint64(v___x_914_);
lean_dec_ref(v___x_914_);
v_fold_919_ = lean_uint64_xor(v___x_918_, v___x_917_);
v___x_920_ = 16ULL;
v___x_921_ = lean_uint64_shift_right(v_fold_919_, v___x_920_);
v___x_922_ = lean_uint64_xor(v_fold_919_, v___x_921_);
v___x_923_ = lean_uint64_to_usize(v___x_922_);
v___x_924_ = lean_usize_of_nat(v___x_913_);
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_sub(v___x_924_, v___x_925_);
v___x_927_ = lean_usize_land(v___x_923_, v___x_926_);
v_bkt_928_ = lean_array_uget_borrowed(v_buckets_912_, v___x_927_);
lean_inc(v_bkt_928_);
v___x_929_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_905_, v_a_909_, v_bkt_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_952_; 
lean_inc_ref(v_buckets_912_);
lean_inc(v_size_911_);
v_isSharedCheck_952_ = !lean_is_exclusive(v_m_908_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_953_ = lean_ctor_get(v_m_908_, 1);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_m_908_, 0);
lean_dec(v_unused_954_);
v___x_931_ = v_m_908_;
v_isShared_932_ = v_isSharedCheck_952_;
goto v_resetjp_930_;
}
else
{
lean_dec(v_m_908_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_952_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v_size_x27_934_; lean_object* v___x_935_; lean_object* v_buckets_x27_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_933_ = lean_unsigned_to_nat(1u);
v_size_x27_934_ = lean_nat_add(v_size_911_, v___x_933_);
lean_dec(v_size_911_);
lean_inc(v_bkt_928_);
v___x_935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_935_, 0, v_a_909_);
lean_ctor_set(v___x_935_, 1, v_b_910_);
lean_ctor_set(v___x_935_, 2, v_bkt_928_);
v_buckets_x27_936_ = lean_array_uset(v_buckets_912_, v___x_927_, v___x_935_);
v___x_937_ = lean_unsigned_to_nat(4u);
v___x_938_ = lean_nat_mul(v_size_x27_934_, v___x_937_);
v___x_939_ = lean_unsigned_to_nat(3u);
v___x_940_ = lean_nat_div(v___x_938_, v___x_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_array_get_size(v_buckets_x27_936_);
v___x_942_ = lean_nat_dec_le(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
if (v___x_942_ == 0)
{
lean_object* v_val_943_; lean_object* v___x_945_; 
v_val_943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_906_, v_buckets_x27_936_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_val_943_);
lean_ctor_set(v___x_931_, 0, v_size_x27_934_);
v___x_945_ = v___x_931_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_size_x27_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_val_943_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_929_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
return v___x_946_;
}
}
else
{
lean_object* v___x_949_; 
lean_dec_ref(v_inst_906_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v_buckets_x27_936_);
lean_ctor_set(v___x_931_, 0, v_size_x27_934_);
v___x_949_ = v___x_931_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_size_x27_934_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_buckets_x27_936_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_929_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
return v___x_950_;
}
}
}
}
else
{
lean_object* v___x_955_; 
lean_dec(v_b_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_inst_906_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_929_);
lean_ctor_set(v___x_955_, 1, v_m_908_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_m_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_buckets_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v___x_966_; uint64_t v_fold_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_buckets_960_ = lean_ctor_get(v_m_958_, 1);
v___x_961_ = lean_array_get_size(v_buckets_960_);
lean_inc(v_a_959_);
v___x_962_ = lean_apply_1(v_inst_957_, v_a_959_);
v___x_963_ = 32ULL;
v___x_964_ = lean_unbox_uint64(v___x_962_);
v___x_965_ = lean_uint64_shift_right(v___x_964_, v___x_963_);
v___x_966_ = lean_unbox_uint64(v___x_962_);
lean_dec_ref(v___x_962_);
v_fold_967_ = lean_uint64_xor(v___x_966_, v___x_965_);
v___x_968_ = 16ULL;
v___x_969_ = lean_uint64_shift_right(v_fold_967_, v___x_968_);
v___x_970_ = lean_uint64_xor(v_fold_967_, v___x_969_);
v___x_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = lean_usize_of_nat(v___x_961_);
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_sub(v___x_972_, v___x_973_);
v___x_975_ = lean_usize_land(v___x_971_, v___x_974_);
v___x_976_ = lean_array_uget_borrowed(v_buckets_960_, v___x_975_);
lean_inc(v___x_976_);
v___x_977_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_956_, v_a_959_, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg___boxed(lean_object* v_inst_978_, lean_object* v_inst_979_, lean_object* v_m_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_978_, v_inst_979_, v_m_980_, v_a_981_);
lean_dec_ref(v_m_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_m_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_985_, v_inst_987_, v_m_988_, v_a_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___boxed(lean_object* v_00_u03b1_991_, lean_object* v_00_u03b2_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f(v_00_u03b1_991_, v_00_u03b2_992_, v_inst_993_, v_inst_994_, v_inst_995_, v_m_996_, v_a_997_);
lean_dec_ref(v_m_996_);
return v_res_998_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_m_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_buckets_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint64_t v___x_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; uint64_t v___x_1009_; uint64_t v_fold_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_buckets_1003_ = lean_ctor_get(v_m_1001_, 1);
v___x_1004_ = lean_array_get_size(v_buckets_1003_);
lean_inc(v_a_1002_);
v___x_1005_ = lean_apply_1(v_inst_1000_, v_a_1002_);
v___x_1006_ = 32ULL;
v___x_1007_ = lean_unbox_uint64(v___x_1005_);
v___x_1008_ = lean_uint64_shift_right(v___x_1007_, v___x_1006_);
v___x_1009_ = lean_unbox_uint64(v___x_1005_);
lean_dec_ref(v___x_1005_);
v_fold_1010_ = lean_uint64_xor(v___x_1009_, v___x_1008_);
v___x_1011_ = 16ULL;
v___x_1012_ = lean_uint64_shift_right(v_fold_1010_, v___x_1011_);
v___x_1013_ = lean_uint64_xor(v_fold_1010_, v___x_1012_);
v___x_1014_ = lean_uint64_to_usize(v___x_1013_);
v___x_1015_ = lean_usize_of_nat(v___x_1004_);
v___x_1016_ = ((size_t)1ULL);
v___x_1017_ = lean_usize_sub(v___x_1015_, v___x_1016_);
v___x_1018_ = lean_usize_land(v___x_1014_, v___x_1017_);
v___x_1019_ = lean_array_uget_borrowed(v_buckets_1003_, v___x_1018_);
lean_inc(v___x_1019_);
v___x_1020_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_999_, v_a_1002_, v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___redArg___boxed(lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_m_1023_, lean_object* v_a_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1021_, v_inst_1022_, v_m_1023_, v_a_1024_);
lean_dec_ref(v_m_1023_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains(lean_object* v_00_u03b1_1027_, lean_object* v_00_u03b2_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_m_1031_, lean_object* v_a_1032_){
_start:
{
uint8_t v___x_1033_; 
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1029_, v_inst_1030_, v_m_1031_, v_a_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_res_1040_ = l_Std_DHashMap_Internal_Raw_u2080_contains(v_00_u03b1_1034_, v_00_u03b2_1035_, v_inst_1036_, v_inst_1037_, v_m_1038_, v_a_1039_);
lean_dec_ref(v_m_1038_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_m_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_buckets_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; uint64_t v_fold_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_buckets_1046_ = lean_ctor_get(v_m_1044_, 1);
v___x_1047_ = lean_array_get_size(v_buckets_1046_);
lean_inc(v_a_1045_);
v___x_1048_ = lean_apply_1(v_inst_1043_, v_a_1045_);
v___x_1049_ = 32ULL;
v___x_1050_ = lean_unbox_uint64(v___x_1048_);
v___x_1051_ = lean_uint64_shift_right(v___x_1050_, v___x_1049_);
v___x_1052_ = lean_unbox_uint64(v___x_1048_);
lean_dec_ref(v___x_1048_);
v_fold_1053_ = lean_uint64_xor(v___x_1052_, v___x_1051_);
v___x_1054_ = 16ULL;
v___x_1055_ = lean_uint64_shift_right(v_fold_1053_, v___x_1054_);
v___x_1056_ = lean_uint64_xor(v_fold_1053_, v___x_1055_);
v___x_1057_ = lean_uint64_to_usize(v___x_1056_);
v___x_1058_ = lean_usize_of_nat(v___x_1047_);
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_sub(v___x_1058_, v___x_1059_);
v___x_1061_ = lean_usize_land(v___x_1057_, v___x_1060_);
v___x_1062_ = lean_array_uget_borrowed(v_buckets_1046_, v___x_1061_);
lean_inc(v___x_1062_);
v___x_1063_ = l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1042_, v_a_1045_, v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg___boxed(lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_m_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_1064_, v_inst_1065_, v_m_1066_, v_a_1067_);
lean_dec_ref(v_m_1066_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get(lean_object* v_00_u03b1_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_m_1074_, lean_object* v_a_1075_, lean_object* v_hma_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_1071_, v_inst_1073_, v_m_1074_, v_a_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_m_1083_, lean_object* v_a_1084_, lean_object* v_hma_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_DHashMap_Internal_Raw_u2080_get(v_00_u03b1_1078_, v_00_u03b2_1079_, v_inst_1080_, v_inst_1081_, v_inst_1082_, v_m_1083_, v_a_1084_, v_hma_1085_);
lean_dec_ref(v_m_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_m_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_buckets_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; uint64_t v_fold_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_buckets_1091_ = lean_ctor_get(v_m_1089_, 1);
v___x_1092_ = lean_array_get_size(v_buckets_1091_);
lean_inc(v_a_1090_);
v___x_1093_ = lean_apply_1(v_inst_1088_, v_a_1090_);
v___x_1094_ = 32ULL;
v___x_1095_ = lean_unbox_uint64(v___x_1093_);
v___x_1096_ = lean_uint64_shift_right(v___x_1095_, v___x_1094_);
v___x_1097_ = lean_unbox_uint64(v___x_1093_);
lean_dec_ref(v___x_1093_);
v_fold_1098_ = lean_uint64_xor(v___x_1097_, v___x_1096_);
v___x_1099_ = 16ULL;
v___x_1100_ = lean_uint64_shift_right(v_fold_1098_, v___x_1099_);
v___x_1101_ = lean_uint64_xor(v_fold_1098_, v___x_1100_);
v___x_1102_ = lean_uint64_to_usize(v___x_1101_);
v___x_1103_ = lean_usize_of_nat(v___x_1092_);
v___x_1104_ = ((size_t)1ULL);
v___x_1105_ = lean_usize_sub(v___x_1103_, v___x_1104_);
v___x_1106_ = lean_usize_land(v___x_1102_, v___x_1105_);
v___x_1107_ = lean_array_uget_borrowed(v_buckets_1091_, v___x_1106_);
lean_inc(v___x_1107_);
v___x_1108_ = l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1087_, v_a_1090_, v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg___boxed(lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_m_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1109_, v_inst_1110_, v_m_1111_, v_a_1112_);
lean_dec_ref(v_m_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_m_1118_, lean_object* v_a_1119_, lean_object* v_hma_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1116_, v_inst_1117_, v_m_1118_, v_a_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___boxed(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_m_1126_, lean_object* v_a_1127_, lean_object* v_hma_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry(v_00_u03b1_1122_, v_00_u03b2_1123_, v_inst_1124_, v_inst_1125_, v_m_1126_, v_a_1127_, v_hma_1128_);
lean_dec_ref(v_m_1126_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_m_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_buckets_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint64_t v___x_1137_; uint64_t v___x_1138_; uint64_t v___x_1139_; uint64_t v___x_1140_; uint64_t v_fold_1141_; uint64_t v___x_1142_; uint64_t v___x_1143_; uint64_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; size_t v___x_1147_; size_t v___x_1148_; size_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_buckets_1134_ = lean_ctor_get(v_m_1132_, 1);
v___x_1135_ = lean_array_get_size(v_buckets_1134_);
lean_inc(v_a_1133_);
v___x_1136_ = lean_apply_1(v_inst_1131_, v_a_1133_);
v___x_1137_ = 32ULL;
v___x_1138_ = lean_unbox_uint64(v___x_1136_);
v___x_1139_ = lean_uint64_shift_right(v___x_1138_, v___x_1137_);
v___x_1140_ = lean_unbox_uint64(v___x_1136_);
lean_dec_ref(v___x_1136_);
v_fold_1141_ = lean_uint64_xor(v___x_1140_, v___x_1139_);
v___x_1142_ = 16ULL;
v___x_1143_ = lean_uint64_shift_right(v_fold_1141_, v___x_1142_);
v___x_1144_ = lean_uint64_xor(v_fold_1141_, v___x_1143_);
v___x_1145_ = lean_uint64_to_usize(v___x_1144_);
v___x_1146_ = lean_usize_of_nat(v___x_1135_);
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_sub(v___x_1146_, v___x_1147_);
v___x_1149_ = lean_usize_land(v___x_1145_, v___x_1148_);
v___x_1150_ = lean_array_uget_borrowed(v_buckets_1134_, v___x_1149_);
lean_inc(v___x_1150_);
v___x_1151_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_1130_, v_a_1133_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg___boxed(lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_m_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1152_, v_inst_1153_, v_m_1154_, v_a_1155_);
lean_dec_ref(v_m_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1159_, v_inst_1160_, v_m_1161_, v_a_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(v_00_u03b1_1164_, v_00_u03b2_1165_, v_inst_1166_, v_inst_1167_, v_m_1168_, v_a_1169_);
lean_dec_ref(v_m_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_m_1173_, lean_object* v_a_1174_, lean_object* v_fallback_1175_){
_start:
{
lean_object* v_buckets_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v_fold_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_buckets_1176_ = lean_ctor_get(v_m_1173_, 1);
v___x_1177_ = lean_array_get_size(v_buckets_1176_);
lean_inc(v_a_1174_);
v___x_1178_ = lean_apply_1(v_inst_1172_, v_a_1174_);
v___x_1179_ = 32ULL;
v___x_1180_ = lean_unbox_uint64(v___x_1178_);
v___x_1181_ = lean_uint64_shift_right(v___x_1180_, v___x_1179_);
v___x_1182_ = lean_unbox_uint64(v___x_1178_);
lean_dec_ref(v___x_1178_);
v_fold_1183_ = lean_uint64_xor(v___x_1182_, v___x_1181_);
v___x_1184_ = 16ULL;
v___x_1185_ = lean_uint64_shift_right(v_fold_1183_, v___x_1184_);
v___x_1186_ = lean_uint64_xor(v_fold_1183_, v___x_1185_);
v___x_1187_ = lean_uint64_to_usize(v___x_1186_);
v___x_1188_ = lean_usize_of_nat(v___x_1177_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_sub(v___x_1188_, v___x_1189_);
v___x_1191_ = lean_usize_land(v___x_1187_, v___x_1190_);
v___x_1192_ = lean_array_uget_borrowed(v_buckets_1176_, v___x_1191_);
lean_inc(v___x_1192_);
v___x_1193_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(v_inst_1171_, v_a_1174_, v_fallback_1175_, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg___boxed(lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_m_1196_, lean_object* v_a_1197_, lean_object* v_fallback_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1194_, v_inst_1195_, v_m_1196_, v_a_1197_, v_fallback_1198_);
lean_dec_ref(v_fallback_1198_);
lean_dec_ref(v_m_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_m_1204_, lean_object* v_a_1205_, lean_object* v_fallback_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1202_, v_inst_1203_, v_m_1204_, v_a_1205_, v_fallback_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_m_1212_, lean_object* v_a_1213_, lean_object* v_fallback_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD(v_00_u03b1_1208_, v_00_u03b2_1209_, v_inst_1210_, v_inst_1211_, v_m_1212_, v_a_1213_, v_fallback_1214_);
lean_dec_ref(v_fallback_1214_);
lean_dec_ref(v_m_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_m_1218_, lean_object* v_a_1219_, lean_object* v_inst_1220_){
_start:
{
lean_object* v_buckets_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint64_t v___x_1224_; uint64_t v___x_1225_; uint64_t v___x_1226_; uint64_t v___x_1227_; uint64_t v_fold_1228_; uint64_t v___x_1229_; uint64_t v___x_1230_; uint64_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; size_t v___x_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_buckets_1221_ = lean_ctor_get(v_m_1218_, 1);
v___x_1222_ = lean_array_get_size(v_buckets_1221_);
lean_inc(v_a_1219_);
v___x_1223_ = lean_apply_1(v_inst_1217_, v_a_1219_);
v___x_1224_ = 32ULL;
v___x_1225_ = lean_unbox_uint64(v___x_1223_);
v___x_1226_ = lean_uint64_shift_right(v___x_1225_, v___x_1224_);
v___x_1227_ = lean_unbox_uint64(v___x_1223_);
lean_dec_ref(v___x_1223_);
v_fold_1228_ = lean_uint64_xor(v___x_1227_, v___x_1226_);
v___x_1229_ = 16ULL;
v___x_1230_ = lean_uint64_shift_right(v_fold_1228_, v___x_1229_);
v___x_1231_ = lean_uint64_xor(v_fold_1228_, v___x_1230_);
v___x_1232_ = lean_uint64_to_usize(v___x_1231_);
v___x_1233_ = lean_usize_of_nat(v___x_1222_);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_sub(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_usize_land(v___x_1232_, v___x_1235_);
v___x_1237_ = lean_array_uget_borrowed(v_buckets_1221_, v___x_1236_);
lean_inc(v___x_1237_);
v___x_1238_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(v_inst_1216_, v_a_1219_, v_inst_1220_, v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg___boxed(lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_m_1241_, lean_object* v_a_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1239_, v_inst_1240_, v_m_1241_, v_a_1242_, v_inst_1243_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_m_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_, lean_object* v_inst_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1247_, v_inst_1248_, v_m_1249_, v_a_1250_, v_inst_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(v_00_u03b1_1253_, v_00_u03b2_1254_, v_inst_1255_, v_inst_1256_, v_m_1257_, v_a_1258_, v_inst_1259_);
lean_dec_ref(v_inst_1259_);
lean_dec_ref(v_m_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_m_1263_, lean_object* v_a_1264_, lean_object* v_fallback_1265_){
_start:
{
lean_object* v_buckets_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint64_t v___x_1269_; uint64_t v___x_1270_; uint64_t v___x_1271_; uint64_t v___x_1272_; uint64_t v_fold_1273_; uint64_t v___x_1274_; uint64_t v___x_1275_; uint64_t v___x_1276_; size_t v___x_1277_; size_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_buckets_1266_ = lean_ctor_get(v_m_1263_, 1);
v___x_1267_ = lean_array_get_size(v_buckets_1266_);
lean_inc(v_a_1264_);
v___x_1268_ = lean_apply_1(v_inst_1262_, v_a_1264_);
v___x_1269_ = 32ULL;
v___x_1270_ = lean_unbox_uint64(v___x_1268_);
v___x_1271_ = lean_uint64_shift_right(v___x_1270_, v___x_1269_);
v___x_1272_ = lean_unbox_uint64(v___x_1268_);
lean_dec_ref(v___x_1268_);
v_fold_1273_ = lean_uint64_xor(v___x_1272_, v___x_1271_);
v___x_1274_ = 16ULL;
v___x_1275_ = lean_uint64_shift_right(v_fold_1273_, v___x_1274_);
v___x_1276_ = lean_uint64_xor(v_fold_1273_, v___x_1275_);
v___x_1277_ = lean_uint64_to_usize(v___x_1276_);
v___x_1278_ = lean_usize_of_nat(v___x_1267_);
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_sub(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_usize_land(v___x_1277_, v___x_1280_);
v___x_1282_ = lean_array_uget_borrowed(v_buckets_1266_, v___x_1281_);
lean_inc(v___x_1282_);
v___x_1283_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(v_inst_1261_, v_a_1264_, v_fallback_1265_, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg___boxed(lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_m_1286_, lean_object* v_a_1287_, lean_object* v_fallback_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1284_, v_inst_1285_, v_m_1286_, v_a_1287_, v_fallback_1288_);
lean_dec(v_fallback_1288_);
lean_dec_ref(v_m_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD(lean_object* v_00_u03b1_1290_, lean_object* v_00_u03b2_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_m_1295_, lean_object* v_a_1296_, lean_object* v_fallback_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1292_, v_inst_1294_, v_m_1295_, v_a_1296_, v_fallback_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_m_1304_, lean_object* v_a_1305_, lean_object* v_fallback_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_DHashMap_Internal_Raw_u2080_getD(v_00_u03b1_1299_, v_00_u03b2_1300_, v_inst_1301_, v_inst_1302_, v_inst_1303_, v_m_1304_, v_a_1305_, v_fallback_1306_);
lean_dec(v_fallback_1306_);
lean_dec_ref(v_m_1304_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_m_1310_, lean_object* v_a_1311_, lean_object* v_inst_1312_){
_start:
{
lean_object* v_buckets_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint64_t v___x_1316_; uint64_t v___x_1317_; uint64_t v___x_1318_; uint64_t v___x_1319_; uint64_t v_fold_1320_; uint64_t v___x_1321_; uint64_t v___x_1322_; uint64_t v___x_1323_; size_t v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v_buckets_1313_ = lean_ctor_get(v_m_1310_, 1);
v___x_1314_ = lean_array_get_size(v_buckets_1313_);
lean_inc(v_a_1311_);
v___x_1315_ = lean_apply_1(v_inst_1309_, v_a_1311_);
v___x_1316_ = 32ULL;
v___x_1317_ = lean_unbox_uint64(v___x_1315_);
v___x_1318_ = lean_uint64_shift_right(v___x_1317_, v___x_1316_);
v___x_1319_ = lean_unbox_uint64(v___x_1315_);
lean_dec_ref(v___x_1315_);
v_fold_1320_ = lean_uint64_xor(v___x_1319_, v___x_1318_);
v___x_1321_ = 16ULL;
v___x_1322_ = lean_uint64_shift_right(v_fold_1320_, v___x_1321_);
v___x_1323_ = lean_uint64_xor(v_fold_1320_, v___x_1322_);
v___x_1324_ = lean_uint64_to_usize(v___x_1323_);
v___x_1325_ = lean_usize_of_nat(v___x_1314_);
v___x_1326_ = ((size_t)1ULL);
v___x_1327_ = lean_usize_sub(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_usize_land(v___x_1324_, v___x_1327_);
v___x_1329_ = lean_array_uget_borrowed(v_buckets_1313_, v___x_1328_);
lean_inc(v___x_1329_);
v___x_1330_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(v_inst_1308_, v_a_1311_, v_inst_1312_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___boxed(lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_m_1333_, lean_object* v_a_1334_, lean_object* v_inst_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1331_, v_inst_1332_, v_m_1333_, v_a_1334_, v_inst_1335_);
lean_dec(v_inst_1335_);
lean_dec_ref(v_m_1333_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_inst_1341_, lean_object* v_m_1342_, lean_object* v_a_1343_, lean_object* v_inst_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1339_, v_inst_1341_, v_m_1342_, v_a_1343_, v_inst_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_00_u03b2_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_inst_1350_, lean_object* v_m_1351_, lean_object* v_a_1352_, lean_object* v_inst_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21(v_00_u03b1_1346_, v_00_u03b2_1347_, v_inst_1348_, v_inst_1349_, v_inst_1350_, v_m_1351_, v_a_1352_, v_inst_1353_);
lean_dec(v_inst_1353_);
lean_dec_ref(v_m_1351_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_m_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_size_1359_; lean_object* v_buckets_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint64_t v___x_1363_; uint64_t v___x_1364_; uint64_t v___x_1365_; uint64_t v___x_1366_; uint64_t v_fold_1367_; uint64_t v___x_1368_; uint64_t v___x_1369_; uint64_t v___x_1370_; size_t v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; lean_object* v_bkt_1376_; uint8_t v___x_1377_; 
v_size_1359_ = lean_ctor_get(v_m_1357_, 0);
v_buckets_1360_ = lean_ctor_get(v_m_1357_, 1);
v___x_1361_ = lean_array_get_size(v_buckets_1360_);
lean_inc_n(v_a_1358_, 2);
v___x_1362_ = lean_apply_1(v_inst_1356_, v_a_1358_);
v___x_1363_ = 32ULL;
v___x_1364_ = lean_unbox_uint64(v___x_1362_);
v___x_1365_ = lean_uint64_shift_right(v___x_1364_, v___x_1363_);
v___x_1366_ = lean_unbox_uint64(v___x_1362_);
lean_dec_ref(v___x_1362_);
v_fold_1367_ = lean_uint64_xor(v___x_1366_, v___x_1365_);
v___x_1368_ = 16ULL;
v___x_1369_ = lean_uint64_shift_right(v_fold_1367_, v___x_1368_);
v___x_1370_ = lean_uint64_xor(v_fold_1367_, v___x_1369_);
v___x_1371_ = lean_uint64_to_usize(v___x_1370_);
v___x_1372_ = lean_usize_of_nat(v___x_1361_);
v___x_1373_ = ((size_t)1ULL);
v___x_1374_ = lean_usize_sub(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_usize_land(v___x_1371_, v___x_1374_);
v_bkt_1376_ = lean_array_uget_borrowed(v_buckets_1360_, v___x_1375_);
lean_inc(v_bkt_1376_);
lean_inc_ref(v_inst_1355_);
v___x_1377_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1355_, v_a_1358_, v_bkt_1376_);
if (v___x_1377_ == 0)
{
lean_dec(v_a_1358_);
lean_dec_ref(v_inst_1355_);
return v_m_1357_;
}
else
{
lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1390_; 
lean_inc(v_bkt_1376_);
lean_inc_ref(v_buckets_1360_);
lean_inc(v_size_1359_);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_m_1357_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; lean_object* v_unused_1392_; 
v_unused_1391_ = lean_ctor_get(v_m_1357_, 1);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_m_1357_, 0);
lean_dec(v_unused_1392_);
v___x_1379_ = v_m_1357_;
v_isShared_1380_ = v_isSharedCheck_1390_;
goto v_resetjp_1378_;
}
else
{
lean_dec(v_m_1357_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1390_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v_buckets_x27_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1381_ = lean_box(0);
v_buckets_x27_1382_ = lean_array_uset(v_buckets_1360_, v___x_1375_, v___x_1381_);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_sub(v_size_1359_, v___x_1383_);
lean_dec(v_size_1359_);
v___x_1385_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_1355_, v_a_1358_, v_bkt_1376_);
v___x_1386_ = lean_array_uset(v_buckets_x27_1382_, v___x_1375_, v___x_1385_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___x_1386_);
lean_ctor_set(v___x_1379_, 0, v___x_1384_);
v___x_1388_ = v___x_1379_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase(lean_object* v_00_u03b1_1393_, lean_object* v_00_u03b2_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_m_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1395_, v_inst_1396_, v_m_1397_, v_a_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0(lean_object* v_f_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go(lean_box(0), lean_box(0), lean_box(0), v_f_1400_, v___x_1402_, v_x_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object* v_f_1404_, lean_object* v_m_1405_){
_start:
{
lean_object* v_buckets_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1427_; 
v_buckets_1406_ = lean_ctor_get(v_m_1405_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_m_1405_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_m_1405_, 0);
lean_dec(v_unused_1428_);
v___x_1408_ = v_m_1405_;
v_isShared_1409_ = v_isSharedCheck_1427_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_buckets_1406_);
lean_dec(v_m_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1427_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___f_1410_; lean_object* v___x_1411_; size_t v_sz_1412_; size_t v___x_1413_; lean_object* v_newBuckets_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___f_1410_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1410_, 0, v_f_1404_);
v___x_1411_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_sz_1412_ = lean_array_size(v_buckets_1406_);
v___x_1413_ = ((size_t)0ULL);
v_newBuckets_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___f_1410_, v_sz_1412_, v___x_1413_, v_buckets_1406_);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_newBuckets_1414_);
v___x_1417_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1419_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v_newBuckets_1414_);
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1419_ = v___x_1408_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_newBuckets_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_object* v___f_1421_; size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___f_1421_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_1422_ = lean_usize_of_nat(v___x_1416_);
lean_inc(v_newBuckets_1414_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___f_1421_, v_newBuckets_1414_, v___x_1413_, v___x_1422_, v___x_1415_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 1, v_newBuckets_1414_);
lean_ctor_set(v___x_1408_, 0, v___x_1423_);
v___x_1425_ = v___x_1408_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_newBuckets_1414_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_00_u03b3_1431_, lean_object* v_f_1432_, lean_object* v_m_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1432_, v_m_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0(lean_object* v_f_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go(lean_box(0), lean_box(0), lean_box(0), v_f_1435_, v___x_1437_, v_x_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object* v_f_1439_, lean_object* v_m_1440_){
_start:
{
lean_object* v_size_1441_; lean_object* v_buckets_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1454_; 
v_size_1441_ = lean_ctor_get(v_m_1440_, 0);
v_buckets_1442_ = lean_ctor_get(v_m_1440_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_m_1440_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1444_ = v_m_1440_;
v_isShared_1445_ = v_isSharedCheck_1454_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_buckets_1442_);
lean_inc(v_size_1441_);
lean_dec(v_m_1440_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1454_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___f_1446_; lean_object* v___x_1447_; size_t v_sz_1448_; size_t v___x_1449_; lean_object* v_newBuckets_1450_; lean_object* v___x_1452_; 
v___f_1446_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1446_, 0, v_f_1439_);
v___x_1447_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_sz_1448_ = lean_array_size(v_buckets_1442_);
v___x_1449_ = ((size_t)0ULL);
v_newBuckets_1450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1447_, v___f_1446_, v_sz_1448_, v___x_1449_, v_buckets_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v_newBuckets_1450_);
v___x_1452_ = v___x_1444_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_size_1441_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_newBuckets_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map(lean_object* v_00_u03b1_1455_, lean_object* v_00_u03b2_1456_, lean_object* v_00_u03b3_1457_, lean_object* v_f_1458_, lean_object* v_m_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1458_, v_m_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0(lean_object* v_f_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_box(0);
v___x_1464_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go(lean_box(0), lean_box(0), v_f_1461_, v___x_1463_, v_x_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object* v_f_1465_, lean_object* v_m_1466_){
_start:
{
lean_object* v_buckets_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1488_; 
v_buckets_1467_ = lean_ctor_get(v_m_1466_, 1);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_m_1466_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v_m_1466_, 0);
lean_dec(v_unused_1489_);
v___x_1469_ = v_m_1466_;
v_isShared_1470_ = v_isSharedCheck_1488_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_buckets_1467_);
lean_dec(v_m_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1488_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___f_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v_newBuckets_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___f_1471_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1471_, 0, v_f_1465_);
v___x_1472_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_sz_1473_ = lean_array_size(v_buckets_1467_);
v___x_1474_ = ((size_t)0ULL);
v_newBuckets_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1472_, v___f_1471_, v_sz_1473_, v___x_1474_, v_buckets_1467_);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get_size(v_newBuckets_1475_);
v___x_1478_ = lean_nat_dec_lt(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1480_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v_newBuckets_1475_);
lean_ctor_set(v___x_1469_, 0, v___x_1476_);
v___x_1480_ = v___x_1469_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_newBuckets_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
else
{
lean_object* v___f_1482_; size_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___f_1482_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_1483_ = lean_usize_of_nat(v___x_1477_);
lean_inc(v_newBuckets_1475_);
v___x_1484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1472_, v___f_1482_, v_newBuckets_1475_, v___x_1474_, v___x_1483_, v___x_1476_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v_newBuckets_1475_);
lean_ctor_set(v___x_1469_, 0, v___x_1484_);
v___x_1486_ = v___x_1469_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_newBuckets_1475_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter(lean_object* v_00_u03b1_1490_, lean_object* v_00_u03b2_1491_, lean_object* v_f_1492_, lean_object* v_m_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1492_, v_m_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0(lean_object* v_inst_1495_, lean_object* v_inst_1496_, lean_object* v_x_1497_, lean_object* v_____s_1498_){
_start:
{
lean_object* v_fst_1499_; lean_object* v_snd_1500_; lean_object* v_r_1501_; lean_object* v___x_1502_; 
v_fst_1499_ = lean_ctor_get(v_x_1497_, 0);
lean_inc(v_fst_1499_);
v_snd_1500_ = lean_ctor_get(v_x_1497_, 1);
lean_inc(v_snd_1500_);
lean_dec_ref(v_x_1497_);
v_r_1501_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1495_, v_inst_1496_, v_____s_1498_, v_fst_1499_, v_snd_1500_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_r_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object* v_inst_1503_, lean_object* v_inst_1504_, lean_object* v_inst_1505_, lean_object* v_m_1506_, lean_object* v_l_1507_){
_start:
{
lean_object* v___f_1508_; lean_object* v___x_1509_; 
v___f_1508_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1508_, 0, v_inst_1504_);
lean_closure_set(v___f_1508_, 1, v_inst_1505_);
v___x_1509_ = lean_apply_4(v_inst_1503_, lean_box(0), v_l_1507_, v_m_1506_, v___f_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany(lean_object* v_00_u03b1_1510_, lean_object* v_00_u03b2_1511_, lean_object* v_00_u03c1_1512_, lean_object* v_inst_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_m_1516_, lean_object* v_l_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_1513_, v_inst_1514_, v_inst_1515_, v_m_1516_, v_l_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0(lean_object* v_inst_1519_, lean_object* v_inst_1520_, lean_object* v_x_1521_, lean_object* v_____s_1522_){
_start:
{
lean_object* v_fst_1523_; lean_object* v_r_1524_; lean_object* v___x_1525_; 
v_fst_1523_ = lean_ctor_get(v_x_1521_, 0);
lean_inc(v_fst_1523_);
lean_dec_ref(v_x_1521_);
v_r_1524_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1519_, v_inst_1520_, v_____s_1522_, v_fst_1523_);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_r_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_m_1529_, lean_object* v_l_1530_){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; 
v___f_1531_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1531_, 0, v_inst_1527_);
lean_closure_set(v___f_1531_, 1, v_inst_1528_);
v___x_1532_ = lean_apply_4(v_inst_1526_, lean_box(0), v_l_1530_, v_m_1529_, v___f_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_00_u03c1_1535_, lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_m_1539_, lean_object* v_l_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_1536_, v_inst_1537_, v_inst_1538_, v_m_1539_, v_l_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0(lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_x_1544_, lean_object* v_____s_1545_){
_start:
{
lean_object* v_fst_1546_; lean_object* v_snd_1547_; lean_object* v_r_1548_; lean_object* v___x_1549_; 
v_fst_1546_ = lean_ctor_get(v_x_1544_, 0);
lean_inc(v_fst_1546_);
v_snd_1547_ = lean_ctor_get(v_x_1544_, 1);
lean_inc(v_snd_1547_);
lean_dec_ref(v_x_1544_);
v_r_1548_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1542_, v_inst_1543_, v_____s_1545_, v_fst_1546_, v_snd_1547_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v_r_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg(lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_inst_1552_, lean_object* v_m_1553_, lean_object* v_l_1554_){
_start:
{
lean_object* v___f_1555_; lean_object* v___x_1556_; 
v___f_1555_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1555_, 0, v_inst_1551_);
lean_closure_set(v___f_1555_, 1, v_inst_1552_);
v___x_1556_ = lean_apply_4(v_inst_1550_, lean_box(0), v_l_1554_, v_m_1553_, v___f_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew(lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_00_u03c1_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_m_1563_, lean_object* v_l_1564_){
_start:
{
lean_object* v___f_1565_; lean_object* v___x_1566_; 
v___f_1565_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1565_, 0, v_inst_1561_);
lean_closure_set(v___f_1565_, 1, v_inst_1562_);
v___x_1566_ = lean_apply_4(v_inst_1560_, lean_box(0), v_l_1564_, v_m_1563_, v___f_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_m_1569_, lean_object* v_sofar_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v___x_1572_; 
lean_inc_ref(v_inst_1568_);
lean_inc_ref(v_inst_1567_);
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1567_, v_inst_1568_, v_m_1569_, v_k_1571_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec_ref(v_inst_1568_);
lean_dec_ref(v_inst_1567_);
return v_sofar_1570_;
}
else
{
lean_object* v_val_1573_; lean_object* v_fst_1574_; lean_object* v_snd_1575_; lean_object* v___x_1576_; 
v_val_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v_fst_1574_ = lean_ctor_get(v_val_1573_, 0);
lean_inc(v_fst_1574_);
v_snd_1575_ = lean_ctor_get(v_val_1573_, 1);
lean_inc(v_snd_1575_);
lean_dec(v_val_1573_);
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1567_, v_inst_1568_, v_sofar_1570_, v_fst_1574_, v_snd_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg___boxed(lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_m_1579_, lean_object* v_sofar_1580_, lean_object* v_k_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(v_inst_1577_, v_inst_1578_, v_m_1579_, v_sofar_1580_, v_k_1581_);
lean_dec_ref(v_m_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_m_1587_, lean_object* v_sofar_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v___x_1590_; 
lean_inc_ref(v_inst_1586_);
lean_inc_ref(v_inst_1585_);
v___x_1590_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1585_, v_inst_1586_, v_m_1587_, v_k_1589_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_dec_ref(v_inst_1586_);
lean_dec_ref(v_inst_1585_);
return v_sofar_1588_;
}
else
{
lean_object* v_val_1591_; lean_object* v_fst_1592_; lean_object* v_snd_1593_; lean_object* v___x_1594_; 
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v_fst_1592_ = lean_ctor_get(v_val_1591_, 0);
lean_inc(v_fst_1592_);
v_snd_1593_ = lean_ctor_get(v_val_1591_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_val_1591_);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1585_, v_inst_1586_, v_sofar_1588_, v_fst_1592_, v_snd_1593_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___boxed(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_m_1599_, lean_object* v_sofar_1600_, lean_object* v_k_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(v_00_u03b1_1595_, v_00_u03b2_1596_, v_inst_1597_, v_inst_1598_, v_m_1599_, v_sofar_1600_, v_k_1601_);
lean_dec_ref(v_m_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_m_u2081_1605_, lean_object* v_x1_1606_, lean_object* v_x2_1607_, lean_object* v_x3_1608_){
_start:
{
lean_object* v___x_1609_; 
lean_inc_ref(v_inst_1604_);
lean_inc_ref(v_inst_1603_);
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1603_, v_inst_1604_, v_m_u2081_1605_, v_x2_1607_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_dec_ref(v_inst_1604_);
lean_dec_ref(v_inst_1603_);
return v_x1_1606_;
}
else
{
lean_object* v_val_1610_; lean_object* v_fst_1611_; lean_object* v_snd_1612_; lean_object* v___x_1613_; 
v_val_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v_fst_1611_ = lean_ctor_get(v_val_1610_, 0);
lean_inc(v_fst_1611_);
v_snd_1612_ = lean_ctor_get(v_val_1610_, 1);
lean_inc(v_snd_1612_);
lean_dec(v_val_1610_);
v___x_1613_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1603_, v_inst_1604_, v_x1_1606_, v_fst_1611_, v_snd_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed(lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_m_u2081_1616_, lean_object* v_x1_1617_, lean_object* v_x2_1618_, lean_object* v_x3_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(v_inst_1614_, v_inst_1615_, v_m_u2081_1616_, v_x1_1617_, v_x2_1618_, v_x3_1619_);
lean_dec(v_x3_1619_);
lean_dec_ref(v_m_u2081_1616_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1(lean_object* v___x_1621_, lean_object* v___f_1622_, lean_object* v_acc_1623_, lean_object* v_l_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1621_, v___f_1622_, v_acc_1623_, v_l_1624_);
return v___x_1625_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_unsigned_to_nat(16u);
v___x_1628_ = lean_mk_array(v___x_1627_, v___x_1626_);
return v___x_1628_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___x_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_m_u2081_1634_, lean_object* v_m_u2082_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v_buckets_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1636_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_buckets_1637_ = lean_ctor_get(v_m_u2082_1635_, 1);
lean_inc_ref(v_buckets_1637_);
lean_dec_ref(v_m_u2082_1635_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1);
v___x_1640_ = lean_array_get_size(v_buckets_1637_);
v___x_1641_ = lean_nat_dec_lt(v___x_1638_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_dec_ref(v_buckets_1637_);
lean_dec_ref(v_m_u2081_1634_);
lean_dec_ref(v_inst_1633_);
lean_dec_ref(v_inst_1632_);
return v___x_1639_;
}
else
{
lean_object* v___f_1642_; lean_object* v___f_1643_; size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v___f_1642_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1642_, 0, v_inst_1632_);
lean_closure_set(v___f_1642_, 1, v_inst_1633_);
lean_closure_set(v___f_1642_, 2, v_m_u2081_1634_);
v___f_1643_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1643_, 0, v___x_1636_);
lean_closure_set(v___f_1643_, 1, v___f_1642_);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = lean_usize_of_nat(v___x_1640_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1636_, v___f_1643_, v_buckets_1637_, v___x_1644_, v___x_1645_, v___x_1639_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller(lean_object* v_00_u03b1_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_m_u2081_1651_, lean_object* v_m_u2082_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(v_inst_1649_, v_inst_1650_, v_m_u2081_1651_, v_m_u2082_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0(lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_a_1656_, lean_object* v_b_1657_, lean_object* v_acc_1658_){
_start:
{
lean_object* v_r_1659_; lean_object* v___x_1660_; 
v_r_1659_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1654_, v_inst_1655_, v_acc_1658_, v_a_1656_, v_b_1657_);
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_r_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1(lean_object* v___x_1661_, lean_object* v___f_1662_, lean_object* v_a_1663_, lean_object* v_x_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1661_, v___f_1662_, v_a_1663_, v___y_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg(lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_m_u2081_1671_, lean_object* v_m_u2082_1672_){
_start:
{
lean_object* v___x_1673_; lean_object* v_size_1674_; lean_object* v_buckets_1675_; lean_object* v_size_1676_; uint8_t v___x_1677_; 
v___x_1673_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_size_1674_ = lean_ctor_get(v_m_u2081_1671_, 0);
v_buckets_1675_ = lean_ctor_get(v_m_u2081_1671_, 1);
v_size_1676_ = lean_ctor_get(v_m_u2082_1672_, 0);
v___x_1677_ = lean_nat_dec_le(v_size_1674_, v_size_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___f_1678_; lean_object* v___x_1679_; 
v___f_1678_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1679_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1678_, v_inst_1669_, v_inst_1670_, v_m_u2081_1671_, v_m_u2082_1672_);
return v___x_1679_;
}
else
{
lean_object* v___f_1680_; lean_object* v___f_1681_; size_t v_sz_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
lean_inc_ref(v_buckets_1675_);
lean_dec_ref(v_m_u2081_1671_);
v___f_1680_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1680_, 0, v_inst_1669_);
lean_closure_set(v___f_1680_, 1, v_inst_1670_);
v___f_1681_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1681_, 0, v___x_1673_);
lean_closure_set(v___f_1681_, 1, v___f_1680_);
v_sz_1682_ = lean_array_size(v_buckets_1675_);
v___x_1683_ = ((size_t)0ULL);
v___x_1684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1673_, v_buckets_1675_, v___f_1681_, v_sz_1682_, v___x_1683_, v_m_u2082_1672_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_m_u2081_1689_, lean_object* v_m_u2082_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v_size_1692_; lean_object* v_buckets_1693_; lean_object* v_size_1694_; uint8_t v___x_1695_; 
v___x_1691_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_size_1692_ = lean_ctor_get(v_m_u2081_1689_, 0);
v_buckets_1693_ = lean_ctor_get(v_m_u2081_1689_, 1);
v_size_1694_ = lean_ctor_get(v_m_u2082_1690_, 0);
v___x_1695_ = lean_nat_dec_le(v_size_1692_, v_size_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___f_1696_; lean_object* v___x_1697_; 
v___f_1696_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1697_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1696_, v_inst_1687_, v_inst_1688_, v_m_u2081_1689_, v_m_u2082_1690_);
return v___x_1697_;
}
else
{
lean_object* v___f_1698_; lean_object* v___f_1699_; size_t v_sz_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
lean_inc_ref(v_buckets_1693_);
lean_dec_ref(v_m_u2081_1689_);
v___f_1698_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1698_, 0, v_inst_1687_);
lean_closure_set(v___f_1698_, 1, v_inst_1688_);
v___f_1699_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1699_, 0, v___x_1691_);
lean_closure_set(v___f_1699_, 1, v___f_1698_);
v_sz_1700_ = lean_array_size(v_buckets_1693_);
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1691_, v_buckets_1693_, v___f_1699_, v_sz_1700_, v___x_1701_, v_m_u2082_1690_);
return v___x_1702_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(lean_object* v_inst_1703_, lean_object* v_inst_1704_, lean_object* v_m_u2082_1705_, lean_object* v_k_1706_, lean_object* v_x_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1703_, v_inst_1704_, v_m_u2082_1705_, v_k_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed(lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_m_u2082_1711_, lean_object* v_k_1712_, lean_object* v_x_1713_){
_start:
{
uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_res_1714_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(v_inst_1709_, v_inst_1710_, v_m_u2082_1711_, v_k_1712_, v_x_1713_);
lean_dec(v_x_1713_);
lean_dec_ref(v_m_u2082_1711_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_m_u2081_1718_, lean_object* v_m_u2082_1719_){
_start:
{
lean_object* v_size_1720_; lean_object* v_size_1721_; uint8_t v___x_1722_; 
v_size_1720_ = lean_ctor_get(v_m_u2081_1718_, 0);
v_size_1721_ = lean_ctor_get(v_m_u2082_1719_, 0);
v___x_1722_ = lean_nat_dec_le(v_size_1720_, v_size_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(v_inst_1716_, v_inst_1717_, v_m_u2081_1718_, v_m_u2082_1719_);
return v___x_1723_;
}
else
{
lean_object* v___f_1724_; lean_object* v___x_1725_; 
v___f_1724_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1724_, 0, v_inst_1716_);
lean_closure_set(v___f_1724_, 1, v_inst_1717_);
lean_closure_set(v___f_1724_, 2, v_m_u2082_1719_);
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1724_, v_m_u2081_1718_);
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter(lean_object* v_00_u03b1_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_m_u2081_1730_, lean_object* v_m_u2082_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1728_, v_inst_1729_, v_m_u2081_1730_, v_m_u2082_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_m_u2082_1736_, uint8_t v___x_1737_, lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v_a_1740_, lean_object* v_b_1741_, lean_object* v_acc_1742_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
lean_inc(v_a_1740_);
v___x_1743_ = lean_apply_1(v_inst_1733_, v_a_1740_);
v___x_1744_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1734_, v_inst_1735_, v_m_u2082_1736_, v_a_1740_);
v___x_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1741_);
v___x_1746_ = l_instBEqOption_beq___redArg(v___x_1743_, v___x_1744_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
lean_dec_ref(v___x_1739_);
v___x_1747_ = lean_box(v___x_1737_);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v___x_1738_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1739_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed(lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_m_u2082_1755_, lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v___x_1758_, lean_object* v_a_1759_, lean_object* v_b_1760_, lean_object* v_acc_1761_){
_start:
{
uint8_t v___x_238__boxed_1762_; lean_object* v_res_1763_; 
v___x_238__boxed_1762_ = lean_unbox(v___x_1756_);
v_res_1763_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(v_inst_1752_, v_inst_1753_, v_inst_1754_, v_m_u2082_1755_, v___x_238__boxed_1762_, v___x_1757_, v___x_1758_, v_a_1759_, v_b_1760_, v_acc_1761_);
lean_dec_ref(v_acc_1761_);
lean_dec_ref(v_m_u2082_1755_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1(lean_object* v___x_1764_, lean_object* v___f_1765_, lean_object* v_a_1766_, lean_object* v_x_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1764_, v___f_1765_, v_a_1766_, v___y_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object* v_inst_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_m_u2081_1776_, lean_object* v_m_u2082_1777_){
_start:
{
lean_object* v_size_1778_; lean_object* v_buckets_1779_; lean_object* v_size_1780_; uint8_t v___x_1781_; 
v_size_1778_ = lean_ctor_get(v_m_u2081_1776_, 0);
lean_inc(v_size_1778_);
v_buckets_1779_ = lean_ctor_get(v_m_u2081_1776_, 1);
lean_inc_ref(v_buckets_1779_);
lean_dec_ref(v_m_u2081_1776_);
v_size_1780_ = lean_ctor_get(v_m_u2082_1777_, 0);
v___x_1781_ = lean_nat_dec_eq(v_size_1778_, v_size_1780_);
lean_dec(v_size_1778_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v_buckets_1779_);
lean_dec_ref(v_m_u2082_1777_);
lean_dec_ref(v_inst_1775_);
lean_dec_ref(v_inst_1774_);
lean_dec_ref(v_inst_1773_);
return v___x_1781_;
}
else
{
uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___f_1788_; size_t v_sz_1789_; size_t v___x_1790_; lean_object* v___x_1791_; lean_object* v_fst_1792_; 
v___x_1782_ = 0;
v___x_1783_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_1784_ = lean_box(0);
v___x_1785_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0));
v___x_1786_ = lean_box(v___x_1782_);
v___f_1787_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1787_, 0, v_inst_1775_);
lean_closure_set(v___f_1787_, 1, v_inst_1773_);
lean_closure_set(v___f_1787_, 2, v_inst_1774_);
lean_closure_set(v___f_1787_, 3, v_m_u2082_1777_);
lean_closure_set(v___f_1787_, 4, v___x_1786_);
lean_closure_set(v___f_1787_, 5, v___x_1784_);
lean_closure_set(v___f_1787_, 6, v___x_1785_);
v___f_1788_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1788_, 0, v___x_1783_);
lean_closure_set(v___f_1788_, 1, v___f_1787_);
v_sz_1789_ = lean_array_size(v_buckets_1779_);
v___x_1790_ = ((size_t)0ULL);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1783_, v_buckets_1779_, v___f_1788_, v_sz_1789_, v___x_1790_, v___x_1785_);
v_fst_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_fst_1792_);
lean_dec(v___x_1791_);
if (lean_obj_tag(v_fst_1792_) == 0)
{
return v___x_1781_;
}
else
{
lean_object* v_val_1793_; uint8_t v___x_1794_; 
v_val_1793_ = lean_ctor_get(v_fst_1792_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v_fst_1792_, 1);
v___x_1794_ = lean_unbox(v_val_1793_);
lean_dec(v_val_1793_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___boxed(lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_m_u2081_1798_, lean_object* v_m_u2082_1799_){
_start:
{
uint8_t v_res_1800_; lean_object* v_r_1801_; 
v_res_1800_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1795_, v_inst_1796_, v_inst_1797_, v_m_u2081_1798_, v_m_u2082_1799_);
v_r_1801_ = lean_box(v_res_1800_);
return v_r_1801_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq(lean_object* v_00_u03b1_1802_, lean_object* v_00_u03b2_1803_, lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_m_u2081_1808_, lean_object* v_m_u2082_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1804_, v_inst_1806_, v_inst_1807_, v_m_u2081_1808_, v_m_u2082_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___boxed(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_m_u2081_1817_, lean_object* v_m_u2082_1818_){
_start:
{
uint8_t v_res_1819_; lean_object* v_r_1820_; 
v_res_1819_ = l_Std_DHashMap_Internal_Raw_u2080_beq(v_00_u03b1_1811_, v_00_u03b2_1812_, v_inst_1813_, v_inst_1814_, v_inst_1815_, v_inst_1816_, v_m_u2081_1817_, v_m_u2082_1818_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_m_u2082_1823_, uint8_t v___x_1824_, lean_object* v_k_1825_, lean_object* v_x_1826_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1821_, v_inst_1822_, v_m_u2082_1823_, v_k_1825_);
if (v___x_1827_ == 0)
{
return v___x_1824_;
}
else
{
uint8_t v___x_1828_; 
v___x_1828_ = 0;
return v___x_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed(lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_m_u2082_1831_, lean_object* v___x_1832_, lean_object* v_k_1833_, lean_object* v_x_1834_){
_start:
{
uint8_t v___x_71__boxed_1835_; uint8_t v_res_1836_; lean_object* v_r_1837_; 
v___x_71__boxed_1835_ = lean_unbox(v___x_1832_);
v_res_1836_ = l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(v_inst_1829_, v_inst_1830_, v_m_u2082_1831_, v___x_71__boxed_1835_, v_k_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec_ref(v_m_u2082_1831_);
v_r_1837_ = lean_box(v_res_1836_);
return v_r_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg(lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_m_u2081_1840_, lean_object* v_m_u2082_1841_){
_start:
{
lean_object* v_size_1842_; lean_object* v_size_1843_; uint8_t v___x_1844_; 
v_size_1842_ = lean_ctor_get(v_m_u2081_1840_, 0);
v_size_1843_ = lean_ctor_get(v_m_u2082_1841_, 0);
v___x_1844_ = lean_nat_dec_le(v_size_1842_, v_size_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___f_1845_; lean_object* v___x_1846_; 
v___f_1845_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1845_, v_inst_1838_, v_inst_1839_, v_m_u2081_1840_, v_m_u2082_1841_);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; lean_object* v___f_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(v___x_1844_);
v___f_1848_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1848_, 0, v_inst_1838_);
lean_closure_set(v___f_1848_, 1, v_inst_1839_);
lean_closure_set(v___f_1848_, 2, v_m_u2082_1841_);
lean_closure_set(v___f_1848_, 3, v___x_1847_);
v___x_1849_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1848_, v_m_u2081_1840_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff(lean_object* v_00_u03b1_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_m_u2081_1854_, lean_object* v_m_u2082_1855_){
_start:
{
lean_object* v_size_1856_; lean_object* v_size_1857_; uint8_t v___x_1858_; 
v_size_1856_ = lean_ctor_get(v_m_u2081_1854_, 0);
v_size_1857_ = lean_ctor_get(v_m_u2082_1855_, 0);
v___x_1858_ = lean_nat_dec_le(v_size_1856_, v_size_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___f_1859_; lean_object* v___x_1860_; 
v___f_1859_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1859_, v_inst_1852_, v_inst_1853_, v_m_u2081_1854_, v_m_u2082_1855_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___x_1863_; 
v___x_1861_ = lean_box(v___x_1858_);
v___f_1862_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1862_, 0, v_inst_1852_);
lean_closure_set(v___f_1862_, 1, v_inst_1853_);
lean_closure_set(v___f_1862_, 2, v_m_u2082_1855_);
lean_closure_set(v___f_1862_, 3, v___x_1861_);
v___x_1863_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1862_, v_m_u2081_1854_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_m_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_buckets_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint64_t v___x_1871_; uint64_t v___x_1872_; uint64_t v___x_1873_; uint64_t v___x_1874_; uint64_t v_fold_1875_; uint64_t v___x_1876_; uint64_t v___x_1877_; uint64_t v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; size_t v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_buckets_1868_ = lean_ctor_get(v_m_1866_, 1);
v___x_1869_ = lean_array_get_size(v_buckets_1868_);
lean_inc(v_a_1867_);
v___x_1870_ = lean_apply_1(v_inst_1865_, v_a_1867_);
v___x_1871_ = 32ULL;
v___x_1872_ = lean_unbox_uint64(v___x_1870_);
v___x_1873_ = lean_uint64_shift_right(v___x_1872_, v___x_1871_);
v___x_1874_ = lean_unbox_uint64(v___x_1870_);
lean_dec_ref(v___x_1870_);
v_fold_1875_ = lean_uint64_xor(v___x_1874_, v___x_1873_);
v___x_1876_ = 16ULL;
v___x_1877_ = lean_uint64_shift_right(v_fold_1875_, v___x_1876_);
v___x_1878_ = lean_uint64_xor(v_fold_1875_, v___x_1877_);
v___x_1879_ = lean_uint64_to_usize(v___x_1878_);
v___x_1880_ = lean_usize_of_nat(v___x_1869_);
v___x_1881_ = ((size_t)1ULL);
v___x_1882_ = lean_usize_sub(v___x_1880_, v___x_1881_);
v___x_1883_ = lean_usize_land(v___x_1879_, v___x_1882_);
v___x_1884_ = lean_array_uget_borrowed(v_buckets_1868_, v___x_1883_);
lean_inc(v___x_1884_);
v___x_1885_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1864_, v_a_1867_, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg___boxed(lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_m_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1886_, v_inst_1887_, v_m_1888_, v_a_1889_);
lean_dec_ref(v_m_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(lean_object* v_00_u03b1_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_m_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1893_, v_inst_1894_, v_m_1895_, v_a_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___boxed(lean_object* v_00_u03b1_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_m_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(v_00_u03b1_1898_, v_00_u03b2_1899_, v_inst_1900_, v_inst_1901_, v_m_1902_, v_a_1903_);
lean_dec_ref(v_m_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_m_u2082_1907_, lean_object* v_inst_1908_, uint8_t v___x_1909_, lean_object* v___x_1910_, lean_object* v___x_1911_, lean_object* v_a_1912_, lean_object* v_b_1913_, lean_object* v_acc_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1905_, v_inst_1906_, v_m_u2082_1907_, v_a_1912_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1913_);
v___x_1917_ = l_instBEqOption_beq___redArg(v_inst_1908_, v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v___x_1911_);
v___x_1918_ = lean_box(v___x_1909_);
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1910_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1911_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed(lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_m_u2082_1925_, lean_object* v_inst_1926_, lean_object* v___x_1927_, lean_object* v___x_1928_, lean_object* v___x_1929_, lean_object* v_a_1930_, lean_object* v_b_1931_, lean_object* v_acc_1932_){
_start:
{
uint8_t v___x_231__boxed_1933_; lean_object* v_res_1934_; 
v___x_231__boxed_1933_ = lean_unbox(v___x_1927_);
v_res_1934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(v_inst_1923_, v_inst_1924_, v_m_u2082_1925_, v_inst_1926_, v___x_231__boxed_1933_, v___x_1928_, v___x_1929_, v_a_1930_, v_b_1931_, v_acc_1932_);
lean_dec_ref(v_acc_1932_);
lean_dec_ref(v_m_u2082_1925_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_m_u2081_1938_, lean_object* v_m_u2082_1939_){
_start:
{
lean_object* v_size_1940_; lean_object* v_buckets_1941_; lean_object* v_size_1942_; uint8_t v___x_1943_; 
v_size_1940_ = lean_ctor_get(v_m_u2081_1938_, 0);
lean_inc(v_size_1940_);
v_buckets_1941_ = lean_ctor_get(v_m_u2081_1938_, 1);
lean_inc_ref(v_buckets_1941_);
lean_dec_ref(v_m_u2081_1938_);
v_size_1942_ = lean_ctor_get(v_m_u2082_1939_, 0);
v___x_1943_ = lean_nat_dec_eq(v_size_1940_, v_size_1942_);
lean_dec(v_size_1940_);
if (v___x_1943_ == 0)
{
lean_dec_ref(v_buckets_1941_);
lean_dec_ref(v_m_u2082_1939_);
lean_dec_ref(v_inst_1937_);
lean_dec_ref(v_inst_1936_);
lean_dec_ref(v_inst_1935_);
return v___x_1943_;
}
else
{
uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; size_t v_sz_1951_; size_t v___x_1952_; lean_object* v___x_1953_; lean_object* v_fst_1954_; 
v___x_1944_ = 0;
v___x_1945_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_1946_ = lean_box(0);
v___x_1947_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0));
v___x_1948_ = lean_box(v___x_1944_);
v___f_1949_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1949_, 0, v_inst_1935_);
lean_closure_set(v___f_1949_, 1, v_inst_1936_);
lean_closure_set(v___f_1949_, 2, v_m_u2082_1939_);
lean_closure_set(v___f_1949_, 3, v_inst_1937_);
lean_closure_set(v___f_1949_, 4, v___x_1948_);
lean_closure_set(v___f_1949_, 5, v___x_1946_);
lean_closure_set(v___f_1949_, 6, v___x_1947_);
v___f_1950_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1950_, 0, v___x_1945_);
lean_closure_set(v___f_1950_, 1, v___f_1949_);
v_sz_1951_ = lean_array_size(v_buckets_1941_);
v___x_1952_ = ((size_t)0ULL);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1945_, v_buckets_1941_, v___f_1950_, v_sz_1951_, v___x_1952_, v___x_1947_);
v_fst_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_fst_1954_);
lean_dec(v___x_1953_);
if (lean_obj_tag(v_fst_1954_) == 0)
{
return v___x_1943_;
}
else
{
lean_object* v_val_1955_; uint8_t v___x_1956_; 
v_val_1955_ = lean_ctor_get(v_fst_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v_fst_1954_, 1);
v___x_1956_ = lean_unbox(v_val_1955_);
lean_dec(v_val_1955_);
return v___x_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___boxed(lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_m_u2081_1960_, lean_object* v_m_u2082_1961_){
_start:
{
uint8_t v_res_1962_; lean_object* v_r_1963_; 
v_res_1962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1957_, v_inst_1958_, v_inst_1959_, v_m_u2081_1960_, v_m_u2082_1961_);
v_r_1963_ = lean_box(v_res_1962_);
return v_r_1963_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq(lean_object* v_00_u03b1_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_m_u2081_1969_, lean_object* v_m_u2082_1970_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1966_, v_inst_1967_, v_inst_1968_, v_m_u2081_1969_, v_m_u2082_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___boxed(lean_object* v_00_u03b1_1972_, lean_object* v_00_u03b2_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_m_u2081_1977_, lean_object* v_m_u2082_1978_){
_start:
{
uint8_t v_res_1979_; lean_object* v_r_1980_; 
v_res_1979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq(v_00_u03b1_1972_, v_00_u03b2_1973_, v_inst_1974_, v_inst_1975_, v_inst_1976_, v_m_u2081_1977_, v_m_u2082_1978_);
v_r_1980_ = lean_box(v_res_1979_);
return v_r_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_m_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_buckets_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint64_t v___x_1988_; uint64_t v___x_1989_; uint64_t v___x_1990_; uint64_t v___x_1991_; uint64_t v_fold_1992_; uint64_t v___x_1993_; uint64_t v___x_1994_; uint64_t v___x_1995_; size_t v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_buckets_1985_ = lean_ctor_get(v_m_1983_, 1);
v___x_1986_ = lean_array_get_size(v_buckets_1985_);
lean_inc(v_a_1984_);
v___x_1987_ = lean_apply_1(v_inst_1982_, v_a_1984_);
v___x_1988_ = 32ULL;
v___x_1989_ = lean_unbox_uint64(v___x_1987_);
v___x_1990_ = lean_uint64_shift_right(v___x_1989_, v___x_1988_);
v___x_1991_ = lean_unbox_uint64(v___x_1987_);
lean_dec_ref(v___x_1987_);
v_fold_1992_ = lean_uint64_xor(v___x_1991_, v___x_1990_);
v___x_1993_ = 16ULL;
v___x_1994_ = lean_uint64_shift_right(v_fold_1992_, v___x_1993_);
v___x_1995_ = lean_uint64_xor(v_fold_1992_, v___x_1994_);
v___x_1996_ = lean_uint64_to_usize(v___x_1995_);
v___x_1997_ = lean_usize_of_nat(v___x_1986_);
v___x_1998_ = ((size_t)1ULL);
v___x_1999_ = lean_usize_sub(v___x_1997_, v___x_1998_);
v___x_2000_ = lean_usize_land(v___x_1996_, v___x_1999_);
v___x_2001_ = lean_array_uget_borrowed(v_buckets_1985_, v___x_2000_);
lean_inc(v___x_2001_);
v___x_2002_ = l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1981_, v_a_1984_, v___x_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg___boxed(lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_m_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_2003_, v_inst_2004_, v_m_2005_, v_a_2006_);
lean_dec_ref(v_m_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get(lean_object* v_00_u03b1_2008_, lean_object* v_00_u03b2_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_m_2012_, lean_object* v_a_2013_, lean_object* v_hma_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_2010_, v_inst_2011_, v_m_2012_, v_a_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___boxed(lean_object* v_00_u03b1_2016_, lean_object* v_00_u03b2_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_m_2020_, lean_object* v_a_2021_, lean_object* v_hma_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get(v_00_u03b1_2016_, v_00_u03b2_2017_, v_inst_2018_, v_inst_2019_, v_m_2020_, v_a_2021_, v_hma_2022_);
lean_dec_ref(v_m_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_m_2026_, lean_object* v_a_2027_, lean_object* v_fallback_2028_){
_start:
{
lean_object* v_buckets_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint64_t v___x_2032_; uint64_t v___x_2033_; uint64_t v___x_2034_; uint64_t v___x_2035_; uint64_t v_fold_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; uint64_t v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; size_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_buckets_2029_ = lean_ctor_get(v_m_2026_, 1);
v___x_2030_ = lean_array_get_size(v_buckets_2029_);
lean_inc(v_a_2027_);
v___x_2031_ = lean_apply_1(v_inst_2025_, v_a_2027_);
v___x_2032_ = 32ULL;
v___x_2033_ = lean_unbox_uint64(v___x_2031_);
v___x_2034_ = lean_uint64_shift_right(v___x_2033_, v___x_2032_);
v___x_2035_ = lean_unbox_uint64(v___x_2031_);
lean_dec_ref(v___x_2031_);
v_fold_2036_ = lean_uint64_xor(v___x_2035_, v___x_2034_);
v___x_2037_ = 16ULL;
v___x_2038_ = lean_uint64_shift_right(v_fold_2036_, v___x_2037_);
v___x_2039_ = lean_uint64_xor(v_fold_2036_, v___x_2038_);
v___x_2040_ = lean_uint64_to_usize(v___x_2039_);
v___x_2041_ = lean_usize_of_nat(v___x_2030_);
v___x_2042_ = ((size_t)1ULL);
v___x_2043_ = lean_usize_sub(v___x_2041_, v___x_2042_);
v___x_2044_ = lean_usize_land(v___x_2040_, v___x_2043_);
v___x_2045_ = lean_array_uget_borrowed(v_buckets_2029_, v___x_2044_);
lean_inc(v___x_2045_);
v___x_2046_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(v_inst_2024_, v_a_2027_, v_fallback_2028_, v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg___boxed(lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_m_2049_, lean_object* v_a_2050_, lean_object* v_fallback_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_2047_, v_inst_2048_, v_m_2049_, v_a_2050_, v_fallback_2051_);
lean_dec(v_fallback_2051_);
lean_dec_ref(v_m_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD(lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_inst_2055_, lean_object* v_inst_2056_, lean_object* v_m_2057_, lean_object* v_a_2058_, lean_object* v_fallback_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_2055_, v_inst_2056_, v_m_2057_, v_a_2058_, v_fallback_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_00_u03b2_2062_, lean_object* v_inst_2063_, lean_object* v_inst_2064_, lean_object* v_m_2065_, lean_object* v_a_2066_, lean_object* v_fallback_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD(v_00_u03b1_2061_, v_00_u03b2_2062_, v_inst_2063_, v_inst_2064_, v_m_2065_, v_a_2066_, v_fallback_2067_);
lean_dec(v_fallback_2067_);
lean_dec_ref(v_m_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_m_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_buckets_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; uint64_t v___x_2077_; uint64_t v___x_2078_; uint64_t v___x_2079_; uint64_t v___x_2080_; uint64_t v_fold_2081_; uint64_t v___x_2082_; uint64_t v___x_2083_; uint64_t v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_buckets_2074_ = lean_ctor_get(v_m_2072_, 1);
v___x_2075_ = lean_array_get_size(v_buckets_2074_);
lean_inc(v_a_2073_);
v___x_2076_ = lean_apply_1(v_inst_2070_, v_a_2073_);
v___x_2077_ = 32ULL;
v___x_2078_ = lean_unbox_uint64(v___x_2076_);
v___x_2079_ = lean_uint64_shift_right(v___x_2078_, v___x_2077_);
v___x_2080_ = lean_unbox_uint64(v___x_2076_);
lean_dec_ref(v___x_2076_);
v_fold_2081_ = lean_uint64_xor(v___x_2080_, v___x_2079_);
v___x_2082_ = 16ULL;
v___x_2083_ = lean_uint64_shift_right(v_fold_2081_, v___x_2082_);
v___x_2084_ = lean_uint64_xor(v_fold_2081_, v___x_2083_);
v___x_2085_ = lean_uint64_to_usize(v___x_2084_);
v___x_2086_ = lean_usize_of_nat(v___x_2075_);
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_sub(v___x_2086_, v___x_2087_);
v___x_2089_ = lean_usize_land(v___x_2085_, v___x_2088_);
v___x_2090_ = lean_array_uget_borrowed(v_buckets_2074_, v___x_2089_);
lean_inc(v___x_2090_);
v___x_2091_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(v_inst_2069_, v_inst_2071_, v_a_2073_, v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___boxed(lean_object* v_inst_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_m_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_2092_, v_inst_2093_, v_inst_2094_, v_m_2095_, v_a_2096_);
lean_dec_ref(v_m_2095_);
lean_dec(v_inst_2094_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(lean_object* v_00_u03b1_2098_, lean_object* v_00_u03b2_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_m_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_2100_, v_inst_2101_, v_inst_2102_, v_m_2103_, v_a_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_m_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(v_00_u03b1_2106_, v_00_u03b2_2107_, v_inst_2108_, v_inst_2109_, v_inst_2110_, v_m_2111_, v_a_2112_);
lean_dec_ref(v_m_2111_);
lean_dec(v_inst_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_m_2116_, lean_object* v_a_2117_, lean_object* v_b_2118_){
_start:
{
lean_object* v_size_2119_; lean_object* v_buckets_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint64_t v___x_2123_; uint64_t v___x_2124_; uint64_t v___x_2125_; uint64_t v___x_2126_; uint64_t v_fold_2127_; uint64_t v___x_2128_; uint64_t v___x_2129_; uint64_t v___x_2130_; size_t v___x_2131_; size_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; lean_object* v_bkt_2136_; lean_object* v___x_2137_; 
v_size_2119_ = lean_ctor_get(v_m_2116_, 0);
v_buckets_2120_ = lean_ctor_get(v_m_2116_, 1);
v___x_2121_ = lean_array_get_size(v_buckets_2120_);
lean_inc_ref(v_inst_2115_);
lean_inc_n(v_a_2117_, 2);
v___x_2122_ = lean_apply_1(v_inst_2115_, v_a_2117_);
v___x_2123_ = 32ULL;
v___x_2124_ = lean_unbox_uint64(v___x_2122_);
v___x_2125_ = lean_uint64_shift_right(v___x_2124_, v___x_2123_);
v___x_2126_ = lean_unbox_uint64(v___x_2122_);
lean_dec_ref(v___x_2122_);
v_fold_2127_ = lean_uint64_xor(v___x_2126_, v___x_2125_);
v___x_2128_ = 16ULL;
v___x_2129_ = lean_uint64_shift_right(v_fold_2127_, v___x_2128_);
v___x_2130_ = lean_uint64_xor(v_fold_2127_, v___x_2129_);
v___x_2131_ = lean_uint64_to_usize(v___x_2130_);
v___x_2132_ = lean_usize_of_nat(v___x_2121_);
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_sub(v___x_2132_, v___x_2133_);
v___x_2135_ = lean_usize_land(v___x_2131_, v___x_2134_);
v_bkt_2136_ = lean_array_uget_borrowed(v_buckets_2120_, v___x_2135_);
lean_inc(v_bkt_2136_);
v___x_2137_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_2114_, v_a_2117_, v_bkt_2136_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2160_; 
lean_inc_ref(v_buckets_2120_);
lean_inc(v_size_2119_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_m_2116_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2161_ = lean_ctor_get(v_m_2116_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_m_2116_, 0);
lean_dec(v_unused_2162_);
v___x_2139_ = v_m_2116_;
v_isShared_2140_ = v_isSharedCheck_2160_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v_m_2116_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2160_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v_size_x27_2142_; lean_object* v___x_2143_; lean_object* v_buckets_x27_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2141_ = lean_unsigned_to_nat(1u);
v_size_x27_2142_ = lean_nat_add(v_size_2119_, v___x_2141_);
lean_dec(v_size_2119_);
lean_inc(v_bkt_2136_);
v___x_2143_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2143_, 0, v_a_2117_);
lean_ctor_set(v___x_2143_, 1, v_b_2118_);
lean_ctor_set(v___x_2143_, 2, v_bkt_2136_);
v_buckets_x27_2144_ = lean_array_uset(v_buckets_2120_, v___x_2135_, v___x_2143_);
v___x_2145_ = lean_unsigned_to_nat(4u);
v___x_2146_ = lean_nat_mul(v_size_x27_2142_, v___x_2145_);
v___x_2147_ = lean_unsigned_to_nat(3u);
v___x_2148_ = lean_nat_div(v___x_2146_, v___x_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_array_get_size(v_buckets_x27_2144_);
v___x_2150_ = lean_nat_dec_le(v___x_2148_, v___x_2149_);
lean_dec(v___x_2148_);
if (v___x_2150_ == 0)
{
lean_object* v_val_2151_; lean_object* v___x_2153_; 
v_val_2151_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2115_, v_buckets_x27_2144_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_val_2151_);
lean_ctor_set(v___x_2139_, 0, v_size_x27_2142_);
v___x_2153_ = v___x_2139_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_size_x27_2142_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_val_2151_);
v___x_2153_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; 
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2137_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
return v___x_2154_;
}
}
else
{
lean_object* v___x_2157_; 
lean_dec_ref(v_inst_2115_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_buckets_x27_2144_);
lean_ctor_set(v___x_2139_, 0, v_size_x27_2142_);
v___x_2157_ = v___x_2139_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_size_x27_2142_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_buckets_x27_2144_);
v___x_2157_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2137_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
return v___x_2158_;
}
}
}
}
else
{
lean_object* v___x_2163_; 
lean_dec(v_b_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_inst_2115_);
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2137_);
lean_ctor_set(v___x_2163_, 1, v_m_2116_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_2164_, lean_object* v_00_u03b2_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_m_2168_, lean_object* v_a_2169_, lean_object* v_b_2170_){
_start:
{
lean_object* v_size_2171_; lean_object* v_buckets_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; uint64_t v___x_2177_; uint64_t v___x_2178_; uint64_t v_fold_2179_; uint64_t v___x_2180_; uint64_t v___x_2181_; uint64_t v___x_2182_; size_t v___x_2183_; size_t v___x_2184_; size_t v___x_2185_; size_t v___x_2186_; size_t v___x_2187_; lean_object* v_bkt_2188_; lean_object* v___x_2189_; 
v_size_2171_ = lean_ctor_get(v_m_2168_, 0);
v_buckets_2172_ = lean_ctor_get(v_m_2168_, 1);
v___x_2173_ = lean_array_get_size(v_buckets_2172_);
lean_inc_ref(v_inst_2167_);
lean_inc_n(v_a_2169_, 2);
v___x_2174_ = lean_apply_1(v_inst_2167_, v_a_2169_);
v___x_2175_ = 32ULL;
v___x_2176_ = lean_unbox_uint64(v___x_2174_);
v___x_2177_ = lean_uint64_shift_right(v___x_2176_, v___x_2175_);
v___x_2178_ = lean_unbox_uint64(v___x_2174_);
lean_dec_ref(v___x_2174_);
v_fold_2179_ = lean_uint64_xor(v___x_2178_, v___x_2177_);
v___x_2180_ = 16ULL;
v___x_2181_ = lean_uint64_shift_right(v_fold_2179_, v___x_2180_);
v___x_2182_ = lean_uint64_xor(v_fold_2179_, v___x_2181_);
v___x_2183_ = lean_uint64_to_usize(v___x_2182_);
v___x_2184_ = lean_usize_of_nat(v___x_2173_);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_sub(v___x_2184_, v___x_2185_);
v___x_2187_ = lean_usize_land(v___x_2183_, v___x_2186_);
v_bkt_2188_ = lean_array_uget_borrowed(v_buckets_2172_, v___x_2187_);
lean_inc(v_bkt_2188_);
v___x_2189_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_2166_, v_a_2169_, v_bkt_2188_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2212_; 
lean_inc_ref(v_buckets_2172_);
lean_inc(v_size_2171_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_m_2168_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2213_ = lean_ctor_get(v_m_2168_, 1);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_m_2168_, 0);
lean_dec(v_unused_2214_);
v___x_2191_ = v_m_2168_;
v_isShared_2192_ = v_isSharedCheck_2212_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v_m_2168_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2212_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v_size_x27_2194_; lean_object* v___x_2195_; lean_object* v_buckets_x27_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2193_ = lean_unsigned_to_nat(1u);
v_size_x27_2194_ = lean_nat_add(v_size_2171_, v___x_2193_);
lean_dec(v_size_2171_);
lean_inc(v_bkt_2188_);
v___x_2195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2195_, 0, v_a_2169_);
lean_ctor_set(v___x_2195_, 1, v_b_2170_);
lean_ctor_set(v___x_2195_, 2, v_bkt_2188_);
v_buckets_x27_2196_ = lean_array_uset(v_buckets_2172_, v___x_2187_, v___x_2195_);
v___x_2197_ = lean_unsigned_to_nat(4u);
v___x_2198_ = lean_nat_mul(v_size_x27_2194_, v___x_2197_);
v___x_2199_ = lean_unsigned_to_nat(3u);
v___x_2200_ = lean_nat_div(v___x_2198_, v___x_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_array_get_size(v_buckets_x27_2196_);
v___x_2202_ = lean_nat_dec_le(v___x_2200_, v___x_2201_);
lean_dec(v___x_2200_);
if (v___x_2202_ == 0)
{
lean_object* v_val_2203_; lean_object* v___x_2205_; 
v_val_2203_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2167_, v_buckets_x27_2196_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v_val_2203_);
lean_ctor_set(v___x_2191_, 0, v_size_x27_2194_);
v___x_2205_ = v___x_2191_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_size_x27_2194_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_val_2203_);
v___x_2205_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2189_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
return v___x_2206_;
}
}
else
{
lean_object* v___x_2209_; 
lean_dec_ref(v_inst_2167_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v_buckets_x27_2196_);
lean_ctor_set(v___x_2191_, 0, v_size_x27_2194_);
v___x_2209_ = v___x_2191_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_size_x27_2194_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_buckets_x27_2196_);
v___x_2209_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; 
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2189_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
return v___x_2210_;
}
}
}
}
else
{
lean_object* v___x_2215_; 
lean_dec(v_b_2170_);
lean_dec(v_a_2169_);
lean_dec_ref(v_inst_2167_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2189_);
lean_ctor_set(v___x_2215_, 1, v_m_2168_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0(lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_x_2218_, lean_object* v_____s_2219_){
_start:
{
lean_object* v_fst_2220_; lean_object* v_snd_2221_; lean_object* v_r_2222_; lean_object* v___x_2223_; 
v_fst_2220_ = lean_ctor_get(v_x_2218_, 0);
lean_inc(v_fst_2220_);
v_snd_2221_ = lean_ctor_get(v_x_2218_, 1);
lean_inc(v_snd_2221_);
lean_dec_ref(v_x_2218_);
v_r_2222_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_2216_, v_inst_2217_, v_____s_2219_, v_fst_2220_, v_snd_2221_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_r_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_m_2227_, lean_object* v_l_2228_){
_start:
{
lean_object* v___f_2229_; lean_object* v___x_2230_; 
v___f_2229_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2229_, 0, v_inst_2225_);
lean_closure_set(v___f_2229_, 1, v_inst_2226_);
v___x_2230_ = lean_apply_4(v_inst_2224_, lean_box(0), v_l_2228_, v_m_2227_, v___f_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany(lean_object* v_00_u03b1_2231_, lean_object* v_00_u03b2_2232_, lean_object* v_00_u03c1_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_m_2237_, lean_object* v_l_2238_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2234_, v_inst_2235_, v_inst_2236_, v_m_2237_, v_l_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_a_2242_, lean_object* v_____s_2243_){
_start:
{
lean_object* v___x_2244_; lean_object* v_r_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_box(0);
v_r_2245_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_2240_, v_inst_2241_, v_____s_2243_, v_a_2242_, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_r_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_m_2250_, lean_object* v_l_2251_){
_start:
{
lean_object* v___f_2252_; lean_object* v___x_2253_; 
v___f_2252_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2252_, 0, v_inst_2248_);
lean_closure_set(v___f_2252_, 1, v_inst_2249_);
v___x_2253_ = lean_apply_4(v_inst_2247_, lean_box(0), v_l_2251_, v_m_2250_, v___f_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2254_, lean_object* v_00_u03c1_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_m_2259_, lean_object* v_l_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2256_, v_inst_2257_, v_inst_2258_, v_m_2259_, v_l_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_m_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_buckets_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint64_t v___x_2269_; uint64_t v___x_2270_; uint64_t v___x_2271_; uint64_t v___x_2272_; uint64_t v_fold_2273_; uint64_t v___x_2274_; uint64_t v___x_2275_; uint64_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_buckets_2266_ = lean_ctor_get(v_m_2264_, 1);
v___x_2267_ = lean_array_get_size(v_buckets_2266_);
lean_inc(v_a_2265_);
v___x_2268_ = lean_apply_1(v_inst_2263_, v_a_2265_);
v___x_2269_ = 32ULL;
v___x_2270_ = lean_unbox_uint64(v___x_2268_);
v___x_2271_ = lean_uint64_shift_right(v___x_2270_, v___x_2269_);
v___x_2272_ = lean_unbox_uint64(v___x_2268_);
lean_dec_ref(v___x_2268_);
v_fold_2273_ = lean_uint64_xor(v___x_2272_, v___x_2271_);
v___x_2274_ = 16ULL;
v___x_2275_ = lean_uint64_shift_right(v_fold_2273_, v___x_2274_);
v___x_2276_ = lean_uint64_xor(v_fold_2273_, v___x_2275_);
v___x_2277_ = lean_uint64_to_usize(v___x_2276_);
v___x_2278_ = lean_usize_of_nat(v___x_2267_);
v___x_2279_ = ((size_t)1ULL);
v___x_2280_ = lean_usize_sub(v___x_2278_, v___x_2279_);
v___x_2281_ = lean_usize_land(v___x_2277_, v___x_2280_);
v___x_2282_ = lean_array_uget_borrowed(v_buckets_2266_, v___x_2281_);
lean_inc(v___x_2282_);
v___x_2283_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_2262_, v_a_2265_, v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg___boxed(lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_m_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_2284_, v_inst_2285_, v_m_2286_, v_a_2287_);
lean_dec_ref(v_m_2286_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(lean_object* v_00_u03b1_2289_, lean_object* v_00_u03b2_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_m_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_2291_, v_inst_2292_, v_m_2293_, v_a_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_m_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(v_00_u03b1_2296_, v_00_u03b2_2297_, v_inst_2298_, v_inst_2299_, v_m_2300_, v_a_2301_);
lean_dec_ref(v_m_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_m_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_buckets_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v_fold_2314_; uint64_t v___x_2315_; uint64_t v___x_2316_; uint64_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_buckets_2307_ = lean_ctor_get(v_m_2305_, 1);
v___x_2308_ = lean_array_get_size(v_buckets_2307_);
lean_inc(v_a_2306_);
v___x_2309_ = lean_apply_1(v_inst_2304_, v_a_2306_);
v___x_2310_ = 32ULL;
v___x_2311_ = lean_unbox_uint64(v___x_2309_);
v___x_2312_ = lean_uint64_shift_right(v___x_2311_, v___x_2310_);
v___x_2313_ = lean_unbox_uint64(v___x_2309_);
lean_dec_ref(v___x_2309_);
v_fold_2314_ = lean_uint64_xor(v___x_2313_, v___x_2312_);
v___x_2315_ = 16ULL;
v___x_2316_ = lean_uint64_shift_right(v_fold_2314_, v___x_2315_);
v___x_2317_ = lean_uint64_xor(v_fold_2314_, v___x_2316_);
v___x_2318_ = lean_uint64_to_usize(v___x_2317_);
v___x_2319_ = lean_usize_of_nat(v___x_2308_);
v___x_2320_ = ((size_t)1ULL);
v___x_2321_ = lean_usize_sub(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_usize_land(v___x_2318_, v___x_2321_);
v___x_2323_ = lean_array_uget_borrowed(v_buckets_2307_, v___x_2322_);
lean_inc(v___x_2323_);
v___x_2324_ = l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_2303_, v_a_2306_, v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg___boxed(lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_m_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_2325_, v_inst_2326_, v_m_2327_, v_a_2328_);
lean_dec_ref(v_m_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey(lean_object* v_00_u03b1_2330_, lean_object* v_00_u03b2_2331_, lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_m_2334_, lean_object* v_a_2335_, lean_object* v_hma_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_2332_, v_inst_2333_, v_m_2334_, v_a_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_00_u03b2_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_m_2342_, lean_object* v_a_2343_, lean_object* v_hma_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Std_DHashMap_Internal_Raw_u2080_getKey(v_00_u03b1_2338_, v_00_u03b2_2339_, v_inst_2340_, v_inst_2341_, v_m_2342_, v_a_2343_, v_hma_2344_);
lean_dec_ref(v_m_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_m_2348_, lean_object* v_a_2349_, lean_object* v_fallback_2350_){
_start:
{
lean_object* v_buckets_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; uint64_t v___x_2354_; uint64_t v___x_2355_; uint64_t v___x_2356_; uint64_t v___x_2357_; uint64_t v_fold_2358_; uint64_t v___x_2359_; uint64_t v___x_2360_; uint64_t v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; size_t v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_buckets_2351_ = lean_ctor_get(v_m_2348_, 1);
v___x_2352_ = lean_array_get_size(v_buckets_2351_);
lean_inc(v_a_2349_);
v___x_2353_ = lean_apply_1(v_inst_2347_, v_a_2349_);
v___x_2354_ = 32ULL;
v___x_2355_ = lean_unbox_uint64(v___x_2353_);
v___x_2356_ = lean_uint64_shift_right(v___x_2355_, v___x_2354_);
v___x_2357_ = lean_unbox_uint64(v___x_2353_);
lean_dec_ref(v___x_2353_);
v_fold_2358_ = lean_uint64_xor(v___x_2357_, v___x_2356_);
v___x_2359_ = 16ULL;
v___x_2360_ = lean_uint64_shift_right(v_fold_2358_, v___x_2359_);
v___x_2361_ = lean_uint64_xor(v_fold_2358_, v___x_2360_);
v___x_2362_ = lean_uint64_to_usize(v___x_2361_);
v___x_2363_ = lean_usize_of_nat(v___x_2352_);
v___x_2364_ = ((size_t)1ULL);
v___x_2365_ = lean_usize_sub(v___x_2363_, v___x_2364_);
v___x_2366_ = lean_usize_land(v___x_2362_, v___x_2365_);
v___x_2367_ = lean_array_uget_borrowed(v_buckets_2351_, v___x_2366_);
lean_inc(v___x_2367_);
v___x_2368_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(v_inst_2346_, v_a_2349_, v_fallback_2350_, v___x_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg___boxed(lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_m_2371_, lean_object* v_a_2372_, lean_object* v_fallback_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_2369_, v_inst_2370_, v_m_2371_, v_a_2372_, v_fallback_2373_);
lean_dec(v_fallback_2373_);
lean_dec_ref(v_m_2371_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD(lean_object* v_00_u03b1_2375_, lean_object* v_00_u03b2_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_m_2379_, lean_object* v_a_2380_, lean_object* v_fallback_2381_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_2377_, v_inst_2378_, v_m_2379_, v_a_2380_, v_fallback_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_00_u03b2_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_m_2387_, lean_object* v_a_2388_, lean_object* v_fallback_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD(v_00_u03b1_2383_, v_00_u03b2_2384_, v_inst_2385_, v_inst_2386_, v_m_2387_, v_a_2388_, v_fallback_2389_);
lean_dec(v_fallback_2389_);
lean_dec_ref(v_m_2387_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_m_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_buckets_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint64_t v___x_2399_; uint64_t v___x_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; uint64_t v_fold_2403_; uint64_t v___x_2404_; uint64_t v___x_2405_; uint64_t v___x_2406_; size_t v___x_2407_; size_t v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_buckets_2396_ = lean_ctor_get(v_m_2394_, 1);
v___x_2397_ = lean_array_get_size(v_buckets_2396_);
lean_inc(v_a_2395_);
v___x_2398_ = lean_apply_1(v_inst_2392_, v_a_2395_);
v___x_2399_ = 32ULL;
v___x_2400_ = lean_unbox_uint64(v___x_2398_);
v___x_2401_ = lean_uint64_shift_right(v___x_2400_, v___x_2399_);
v___x_2402_ = lean_unbox_uint64(v___x_2398_);
lean_dec_ref(v___x_2398_);
v_fold_2403_ = lean_uint64_xor(v___x_2402_, v___x_2401_);
v___x_2404_ = 16ULL;
v___x_2405_ = lean_uint64_shift_right(v_fold_2403_, v___x_2404_);
v___x_2406_ = lean_uint64_xor(v_fold_2403_, v___x_2405_);
v___x_2407_ = lean_uint64_to_usize(v___x_2406_);
v___x_2408_ = lean_usize_of_nat(v___x_2397_);
v___x_2409_ = ((size_t)1ULL);
v___x_2410_ = lean_usize_sub(v___x_2408_, v___x_2409_);
v___x_2411_ = lean_usize_land(v___x_2407_, v___x_2410_);
v___x_2412_ = lean_array_uget_borrowed(v_buckets_2396_, v___x_2411_);
lean_inc(v___x_2412_);
v___x_2413_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(v_inst_2391_, v_inst_2393_, v_a_2395_, v___x_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___boxed(lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_m_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_m_2417_, v_a_2418_);
lean_dec_ref(v_m_2417_);
lean_dec(v_inst_2416_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(lean_object* v_00_u03b1_2420_, lean_object* v_00_u03b2_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_m_2425_, lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_2422_, v_inst_2423_, v_inst_2424_, v_m_2425_, v_a_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___boxed(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_m_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(v_00_u03b1_2428_, v_00_u03b2_2429_, v_inst_2430_, v_inst_2431_, v_inst_2432_, v_m_2433_, v_a_2434_);
lean_dec_ref(v_m_2433_);
lean_dec(v_inst_2432_);
return v_res_2435_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Power2_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawDef(uint8_t builtin);
lean_object* initialize_Std_Data_Internal_List_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Index(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Internal_List_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Power2_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_Defs(builtin);
}
#ifdef __cplusplus
}
#endif
