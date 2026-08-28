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
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* v___f_71_; uint8_t v___x_72_; 
v___f_71_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_72_ = lean_nat_dec_le(v___x_68_, v___x_68_);
if (v___x_72_ == 0)
{
if (v___x_70_ == 0)
{
lean_dec_ref(v_buckets_66_);
return v___x_67_;
}
else
{
size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((size_t)0ULL);
v___x_74_ = lean_usize_of_nat(v___x_68_);
v___x_75_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_71_, v_buckets_66_, v___x_73_, v___x_74_, v___x_67_);
return v___x_75_;
}
}
else
{
size_t v___x_76_; size_t v___x_77_; lean_object* v___x_78_; 
v___x_76_ = ((size_t)0ULL);
v___x_77_ = lean_usize_of_nat(v___x_68_);
v___x_78_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_69_, v___f_71_, v_buckets_66_, v___x_76_, v___x_77_, v___x_67_);
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_computeSize(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_buckets_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_array_get_size(v_buckets_81_);
v___x_84_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_85_ = lean_nat_dec_lt(v___x_82_, v___x_83_);
if (v___x_85_ == 0)
{
lean_dec_ref(v_buckets_81_);
return v___x_82_;
}
else
{
lean_object* v___f_86_; uint8_t v___x_87_; 
v___f_86_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_87_ = lean_nat_dec_le(v___x_83_, v___x_83_);
if (v___x_87_ == 0)
{
if (v___x_85_ == 0)
{
lean_dec_ref(v_buckets_81_);
return v___x_82_;
}
else
{
size_t v___x_88_; size_t v___x_89_; lean_object* v___x_90_; 
v___x_88_ = ((size_t)0ULL);
v___x_89_ = lean_usize_of_nat(v___x_83_);
v___x_90_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_84_, v___f_86_, v_buckets_81_, v___x_88_, v___x_89_, v___x_82_);
return v___x_90_;
}
}
else
{
size_t v___x_91_; size_t v___x_92_; lean_object* v___x_93_; 
v___x_91_ = ((size_t)0ULL);
v___x_92_ = lean_usize_of_nat(v___x_83_);
v___x_93_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_84_, v___f_86_, v_buckets_81_, v___x_91_, v___x_92_, v___x_82_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(lean_object* v_capacity_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_unsigned_to_nat(4u);
v___x_97_ = lean_nat_mul(v_capacity_94_, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = lean_nat_div(v___x_97_, v___x_98_);
lean_dec(v___x_97_);
v___x_100_ = l_Nat_nextPowerOfTwo(v___x_99_);
lean_dec(v___x_99_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_mk_array(v___x_100_, v___x_101_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_95_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___redArg(v_capacity_104_);
lean_dec(v_capacity_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(lean_object* v_00_u03b1_106_, lean_object* v_00_u03b2_107_, lean_object* v_capacity_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_unsigned_to_nat(4u);
v___x_111_ = lean_nat_mul(v_capacity_108_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(3u);
v___x_113_ = lean_nat_div(v___x_111_, v___x_112_);
lean_dec(v___x_111_);
v___x_114_ = l_Nat_nextPowerOfTwo(v___x_113_);
lean_dec(v___x_113_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_mk_array(v___x_114_, v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_109_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity___boxed(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_capacity_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_DHashMap_Internal_Raw_u2080_emptyWithCapacity(v_00_u03b1_118_, v_00_u03b2_119_, v_capacity_120_);
lean_dec(v_capacity_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_reinsertAux___redArg(lean_object* v_hash_122_, lean_object* v_data_123_, lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint64_t v___x_128_; uint64_t v___x_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v_fold_132_; uint64_t v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_126_ = lean_array_get_size(v_data_123_);
lean_inc(v_a_124_);
v___x_127_ = lean_apply_1(v_hash_122_, v_a_124_);
v___x_128_ = 32ULL;
v___x_129_ = lean_unbox_uint64(v___x_127_);
v___x_130_ = lean_uint64_shift_right(v___x_129_, v___x_128_);
v___x_131_ = lean_unbox_uint64(v___x_127_);
lean_dec_ref(v___x_127_);
v_fold_132_ = lean_uint64_xor(v___x_131_, v___x_130_);
v___x_133_ = 16ULL;
v___x_134_ = lean_uint64_shift_right(v_fold_132_, v___x_133_);
v___x_135_ = lean_uint64_xor(v_fold_132_, v___x_134_);
v___x_136_ = lean_uint64_to_usize(v___x_135_);
v___x_137_ = lean_usize_of_nat(v___x_126_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_sub(v___x_137_, v___x_138_);
v___x_140_ = lean_usize_land(v___x_136_, v___x_139_);
v___x_141_ = lean_array_uget_borrowed(v_data_123_, v___x_140_);
lean_inc(v___x_141_);
v___x_142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_142_, 0, v_a_124_);
lean_ctor_set(v___x_142_, 1, v_b_125_);
lean_ctor_set(v___x_142_, 2, v___x_141_);
v___x_143_ = lean_array_uset(v_data_123_, v___x_140_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_reinsertAux(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_hash_146_, lean_object* v_data_147_, lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint64_t v___x_152_; uint64_t v___x_153_; uint64_t v___x_154_; uint64_t v___x_155_; uint64_t v_fold_156_; uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v___x_159_; size_t v___x_160_; size_t v___x_161_; size_t v___x_162_; size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_150_ = lean_array_get_size(v_data_147_);
lean_inc(v_a_148_);
v___x_151_ = lean_apply_1(v_hash_146_, v_a_148_);
v___x_152_ = 32ULL;
v___x_153_ = lean_unbox_uint64(v___x_151_);
v___x_154_ = lean_uint64_shift_right(v___x_153_, v___x_152_);
v___x_155_ = lean_unbox_uint64(v___x_151_);
lean_dec_ref(v___x_151_);
v_fold_156_ = lean_uint64_xor(v___x_155_, v___x_154_);
v___x_157_ = 16ULL;
v___x_158_ = lean_uint64_shift_right(v_fold_156_, v___x_157_);
v___x_159_ = lean_uint64_xor(v_fold_156_, v___x_158_);
v___x_160_ = lean_uint64_to_usize(v___x_159_);
v___x_161_ = lean_usize_of_nat(v___x_150_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_sub(v___x_161_, v___x_162_);
v___x_164_ = lean_usize_land(v___x_160_, v___x_163_);
v___x_165_ = lean_array_uget_borrowed(v_data_147_, v___x_164_);
lean_inc(v___x_165_);
v___x_166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_166_, 0, v_a_148_);
lean_ctor_set(v___x_166_, 1, v_b_149_);
lean_ctor_set(v___x_166_, 2, v___x_165_);
v___x_167_ = lean_array_uset(v_data_147_, v___x_164_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0(lean_object* v_inst_168_, lean_object* v_x1_169_, lean_object* v_x2_170_, lean_object* v_x3_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v___x_177_; uint64_t v_fold_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v___x_181_; size_t v___x_182_; size_t v___x_183_; size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_172_ = lean_array_get_size(v_x1_169_);
lean_inc(v_x2_170_);
v___x_173_ = lean_apply_1(v_inst_168_, v_x2_170_);
v___x_174_ = 32ULL;
v___x_175_ = lean_unbox_uint64(v___x_173_);
v___x_176_ = lean_uint64_shift_right(v___x_175_, v___x_174_);
v___x_177_ = lean_unbox_uint64(v___x_173_);
lean_dec_ref(v___x_173_);
v_fold_178_ = lean_uint64_xor(v___x_177_, v___x_176_);
v___x_179_ = 16ULL;
v___x_180_ = lean_uint64_shift_right(v_fold_178_, v___x_179_);
v___x_181_ = lean_uint64_xor(v_fold_178_, v___x_180_);
v___x_182_ = lean_uint64_to_usize(v___x_181_);
v___x_183_ = lean_usize_of_nat(v___x_172_);
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_sub(v___x_183_, v___x_184_);
v___x_186_ = lean_usize_land(v___x_182_, v___x_185_);
v___x_187_ = lean_array_uget_borrowed(v_x1_169_, v___x_186_);
lean_inc(v___x_187_);
v___x_188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_188_, 0, v_x2_170_);
lean_ctor_set(v___x_188_, 1, v_x3_171_);
lean_ctor_set(v___x_188_, 2, v___x_187_);
v___x_189_ = lean_array_uset(v_x1_169_, v___x_186_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(lean_object* v_inst_190_, lean_object* v_i_191_, lean_object* v_source_192_, lean_object* v_target_193_){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_array_get_size(v_source_192_);
v___x_195_ = lean_nat_dec_lt(v_i_191_, v___x_194_);
if (v___x_195_ == 0)
{
lean_dec_ref(v_source_192_);
lean_dec(v_i_191_);
lean_dec_ref(v_inst_190_);
return v_target_193_;
}
else
{
lean_object* v___f_196_; lean_object* v_es_197_; lean_object* v___x_198_; lean_object* v_source_199_; lean_object* v___x_200_; lean_object* v_target_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_inc_ref(v_inst_190_);
v___f_196_ = lean_alloc_closure((void*)(l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg___lam__0), 4, 1);
lean_closure_set(v___f_196_, 0, v_inst_190_);
v_es_197_ = lean_array_fget(v_source_192_, v_i_191_);
v___x_198_ = lean_box(0);
v_source_199_ = lean_array_fset(v_source_192_, v_i_191_, v___x_198_);
v___x_200_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_target_201_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_200_, v___f_196_, v_target_193_, v_es_197_);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_i_191_, v___x_202_);
lean_dec(v_i_191_);
v_i_191_ = v___x_203_;
v_source_192_ = v_source_199_;
v_target_193_ = v_target_201_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_inst_207_, lean_object* v_i_208_, lean_object* v_source_209_, lean_object* v_target_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(v_inst_207_, v_i_208_, v_source_209_, v_target_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object* v_inst_212_, lean_object* v_data_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_nbuckets_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_214_ = lean_array_get_size(v_data_213_);
v___x_215_ = lean_unsigned_to_nat(2u);
v_nbuckets_216_ = lean_nat_mul(v___x_214_, v___x_215_);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_box(0);
v___x_219_ = lean_mk_array(v_nbuckets_216_, v___x_218_);
v___x_220_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___redArg(v_inst_212_, v___x_217_, v_data_213_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_, lean_object* v_inst_223_, lean_object* v_data_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_223_, v_data_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___redArg(lean_object* v_inst_226_, lean_object* v_m_227_){
_start:
{
lean_object* v_size_228_; lean_object* v_buckets_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_size_228_ = lean_ctor_get(v_m_227_, 0);
v_buckets_229_ = lean_ctor_get(v_m_227_, 1);
v___x_230_ = lean_unsigned_to_nat(4u);
v___x_231_ = lean_nat_mul(v_size_228_, v___x_230_);
v___x_232_ = lean_unsigned_to_nat(3u);
v___x_233_ = lean_nat_div(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_array_get_size(v_buckets_229_);
v___x_235_ = lean_nat_dec_le(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
if (v___x_235_ == 0)
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
lean_inc_ref(v_buckets_229_);
lean_inc(v_size_228_);
v_isSharedCheck_243_ = !lean_is_exclusive(v_m_227_);
if (v_isSharedCheck_243_ == 0)
{
lean_object* v_unused_244_; lean_object* v_unused_245_; 
v_unused_244_ = lean_ctor_get(v_m_227_, 1);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_m_227_, 0);
lean_dec(v_unused_245_);
v___x_237_ = v_m_227_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_dec(v_m_227_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_val_239_; lean_object* v___x_241_; 
v_val_239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_226_, v_buckets_229_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_val_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_size_228_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_val_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_dec_ref(v_inst_226_);
return v_m_227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_m_250_){
_start:
{
lean_object* v_size_251_; lean_object* v_buckets_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_size_251_ = lean_ctor_get(v_m_250_, 0);
v_buckets_252_ = lean_ctor_get(v_m_250_, 1);
v___x_253_ = lean_unsigned_to_nat(4u);
v___x_254_ = lean_nat_mul(v_size_251_, v___x_253_);
v___x_255_ = lean_unsigned_to_nat(3u);
v___x_256_ = lean_nat_div(v___x_254_, v___x_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_array_get_size(v_buckets_252_);
v___x_258_ = lean_nat_dec_le(v___x_256_, v___x_257_);
lean_dec(v___x_256_);
if (v___x_258_ == 0)
{
lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
lean_inc_ref(v_buckets_252_);
lean_inc(v_size_251_);
v_isSharedCheck_266_ = !lean_is_exclusive(v_m_250_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; lean_object* v_unused_268_; 
v_unused_267_ = lean_ctor_get(v_m_250_, 1);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_m_250_, 0);
lean_dec(v_unused_268_);
v___x_260_ = v_m_250_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_dec(v_m_250_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v_val_262_; lean_object* v___x_264_; 
v_val_262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_249_, v_buckets_252_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 1, v_val_262_);
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_size_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_val_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_dec_ref(v_inst_249_);
return v_m_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_m_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DHashMap_Internal_Raw_u2080_expandIfNecessary(v_00_u03b1_269_, v_00_u03b2_270_, v_inst_271_, v_inst_272_, v_m_273_);
lean_dec_ref(v_inst_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_m_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_size_280_; lean_object* v_buckets_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_326_; 
v_size_280_ = lean_ctor_get(v_m_277_, 0);
v_buckets_281_ = lean_ctor_get(v_m_277_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_m_277_);
if (v_isSharedCheck_326_ == 0)
{
v___x_283_ = v_m_277_;
v_isShared_284_ = v_isSharedCheck_326_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_buckets_281_);
lean_inc(v_size_280_);
lean_dec(v_m_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_326_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v_fold_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v_bkt_300_; uint8_t v___x_301_; 
v___x_285_ = lean_array_get_size(v_buckets_281_);
lean_inc_ref(v_inst_276_);
lean_inc_n(v_a_278_, 2);
v___x_286_ = lean_apply_1(v_inst_276_, v_a_278_);
v___x_287_ = 32ULL;
v___x_288_ = lean_unbox_uint64(v___x_286_);
v___x_289_ = lean_uint64_shift_right(v___x_288_, v___x_287_);
v___x_290_ = lean_unbox_uint64(v___x_286_);
lean_dec_ref(v___x_286_);
v_fold_291_ = lean_uint64_xor(v___x_290_, v___x_289_);
v___x_292_ = 16ULL;
v___x_293_ = lean_uint64_shift_right(v_fold_291_, v___x_292_);
v___x_294_ = lean_uint64_xor(v_fold_291_, v___x_293_);
v___x_295_ = lean_uint64_to_usize(v___x_294_);
v___x_296_ = lean_usize_of_nat(v___x_285_);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_sub(v___x_296_, v___x_297_);
v___x_299_ = lean_usize_land(v___x_295_, v___x_298_);
v_bkt_300_ = lean_array_uget_borrowed(v_buckets_281_, v___x_299_);
lean_inc(v_bkt_300_);
lean_inc_ref(v_inst_275_);
v___x_301_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_275_, v_a_278_, v_bkt_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v_size_x27_303_; lean_object* v___x_304_; lean_object* v_buckets_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
lean_dec_ref(v_inst_275_);
v___x_302_ = lean_unsigned_to_nat(1u);
v_size_x27_303_ = lean_nat_add(v_size_280_, v___x_302_);
lean_dec(v_size_280_);
lean_inc(v_bkt_300_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v_a_278_);
lean_ctor_set(v___x_304_, 1, v_b_279_);
lean_ctor_set(v___x_304_, 2, v_bkt_300_);
v_buckets_x27_305_ = lean_array_uset(v_buckets_281_, v___x_299_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_mul(v_size_x27_303_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(3u);
v___x_309_ = lean_nat_div(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_array_get_size(v_buckets_x27_305_);
v___x_311_ = lean_nat_dec_le(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v_val_312_; lean_object* v___x_314_; 
v_val_312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_276_, v_buckets_x27_305_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_val_312_);
lean_ctor_set(v___x_283_, 0, v_size_x27_303_);
v___x_314_ = v___x_283_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_val_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
lean_object* v___x_317_; 
lean_dec_ref(v_inst_276_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_buckets_x27_305_);
lean_ctor_set(v___x_283_, 0, v_size_x27_303_);
v___x_317_ = v___x_283_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_buckets_x27_305_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v___x_319_; lean_object* v_buckets_x27_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc(v_bkt_300_);
lean_dec_ref(v_inst_276_);
v___x_319_ = lean_box(0);
v_buckets_x27_320_ = lean_array_uset(v_buckets_281_, v___x_299_, v___x_319_);
v___x_321_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_275_, v_a_278_, v_b_279_, v_bkt_300_);
v___x_322_ = lean_array_uset(v_buckets_x27_320_, v___x_299_, v___x_321_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_322_);
v___x_324_ = v___x_283_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_size_280_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert(lean_object* v_00_u03b1_327_, lean_object* v_00_u03b2_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_m_331_, lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_329_, v_inst_330_, v_m_331_, v_a_332_, v_b_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_m_337_, lean_object* v_a_338_, lean_object* v_f_339_){
_start:
{
lean_object* v_size_340_; lean_object* v_buckets_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v___x_347_; uint64_t v_fold_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; size_t v___x_356_; lean_object* v_bucket_357_; uint8_t v___x_358_; 
v_size_340_ = lean_ctor_get(v_m_337_, 0);
v_buckets_341_ = lean_ctor_get(v_m_337_, 1);
v___x_342_ = lean_array_get_size(v_buckets_341_);
lean_inc_n(v_a_338_, 2);
v___x_343_ = lean_apply_1(v_inst_336_, v_a_338_);
v___x_344_ = 32ULL;
v___x_345_ = lean_unbox_uint64(v___x_343_);
v___x_346_ = lean_uint64_shift_right(v___x_345_, v___x_344_);
v___x_347_ = lean_unbox_uint64(v___x_343_);
lean_dec_ref(v___x_343_);
v_fold_348_ = lean_uint64_xor(v___x_347_, v___x_346_);
v___x_349_ = 16ULL;
v___x_350_ = lean_uint64_shift_right(v_fold_348_, v___x_349_);
v___x_351_ = lean_uint64_xor(v_fold_348_, v___x_350_);
v___x_352_ = lean_uint64_to_usize(v___x_351_);
v___x_353_ = lean_usize_of_nat(v___x_342_);
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_sub(v___x_353_, v___x_354_);
v___x_356_ = lean_usize_land(v___x_352_, v___x_355_);
v_bucket_357_ = lean_array_uget_borrowed(v_buckets_341_, v___x_356_);
lean_inc(v_bucket_357_);
lean_inc_ref(v_inst_335_);
v___x_358_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_335_, v_a_338_, v_bucket_357_);
if (v___x_358_ == 0)
{
lean_dec(v_f_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_inst_335_);
return v_m_337_;
}
else
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_369_; 
lean_inc(v_bucket_357_);
lean_inc_ref(v_buckets_341_);
lean_inc(v_size_340_);
v_isSharedCheck_369_ = !lean_is_exclusive(v_m_337_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_370_ = lean_ctor_get(v_m_337_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_m_337_, 0);
lean_dec(v_unused_371_);
v___x_360_ = v_m_337_;
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
else
{
lean_dec(v_m_337_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v_buckets_363_; lean_object* v_bucket_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_362_ = lean_box(0);
v_buckets_363_ = lean_array_uset(v_buckets_341_, v___x_356_, v___x_362_);
v_bucket_364_ = l_Std_DHashMap_Internal_AssocList_modify___redArg(v_inst_335_, v_a_338_, v_f_339_, v_bucket_357_);
v___x_365_ = lean_array_uset(v_buckets_363_, v___x_356_, v_bucket_364_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_365_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_340_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_m_377_, lean_object* v_a_378_, lean_object* v_f_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_modify___redArg(v_inst_374_, v_inst_375_, v_m_377_, v_a_378_, v_f_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_m_383_, lean_object* v_a_384_, lean_object* v_f_385_){
_start:
{
lean_object* v_size_386_; lean_object* v_buckets_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v_fold_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v_bucket_403_; uint8_t v___x_404_; 
v_size_386_ = lean_ctor_get(v_m_383_, 0);
v_buckets_387_ = lean_ctor_get(v_m_383_, 1);
v___x_388_ = lean_array_get_size(v_buckets_387_);
lean_inc_n(v_a_384_, 2);
v___x_389_ = lean_apply_1(v_inst_382_, v_a_384_);
v___x_390_ = 32ULL;
v___x_391_ = lean_unbox_uint64(v___x_389_);
v___x_392_ = lean_uint64_shift_right(v___x_391_, v___x_390_);
v___x_393_ = lean_unbox_uint64(v___x_389_);
lean_dec_ref(v___x_389_);
v_fold_394_ = lean_uint64_xor(v___x_393_, v___x_392_);
v___x_395_ = 16ULL;
v___x_396_ = lean_uint64_shift_right(v_fold_394_, v___x_395_);
v___x_397_ = lean_uint64_xor(v_fold_394_, v___x_396_);
v___x_398_ = lean_uint64_to_usize(v___x_397_);
v___x_399_ = lean_usize_of_nat(v___x_388_);
v___x_400_ = ((size_t)1ULL);
v___x_401_ = lean_usize_sub(v___x_399_, v___x_400_);
v___x_402_ = lean_usize_land(v___x_398_, v___x_401_);
v_bucket_403_ = lean_array_uget_borrowed(v_buckets_387_, v___x_402_);
lean_inc(v_bucket_403_);
lean_inc_ref(v_inst_381_);
v___x_404_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_381_, v_a_384_, v_bucket_403_);
if (v___x_404_ == 0)
{
lean_dec(v_f_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_inst_381_);
return v_m_383_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_415_; 
lean_inc(v_bucket_403_);
lean_inc_ref(v_buckets_387_);
lean_inc(v_size_386_);
v_isSharedCheck_415_ = !lean_is_exclusive(v_m_383_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; 
v_unused_416_ = lean_ctor_get(v_m_383_, 1);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_m_383_, 0);
lean_dec(v_unused_417_);
v___x_406_ = v_m_383_;
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
else
{
lean_dec(v_m_383_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v_buckets_409_; lean_object* v_bucket_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_408_ = lean_box(0);
v_buckets_409_ = lean_array_uset(v_buckets_387_, v___x_402_, v___x_408_);
v_bucket_410_ = l_Std_DHashMap_Internal_AssocList_Const_modify___redArg(v_inst_381_, v_a_384_, v_f_385_, v_bucket_403_);
v___x_411_ = lean_array_uset(v_buckets_409_, v___x_402_, v_bucket_410_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_411_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_size_386_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_00_u03b2_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_f_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_419_, v_inst_421_, v_m_422_, v_a_423_, v_f_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_a_429_, lean_object* v_f_430_){
_start:
{
lean_object* v_size_431_; lean_object* v_buckets_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; uint64_t v___x_438_; uint64_t v_fold_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v___x_442_; size_t v___x_443_; size_t v___x_444_; size_t v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v_bkt_448_; uint8_t v___x_449_; 
v_size_431_ = lean_ctor_get(v_m_428_, 0);
v_buckets_432_ = lean_ctor_get(v_m_428_, 1);
v___x_433_ = lean_array_get_size(v_buckets_432_);
lean_inc_ref(v_inst_427_);
lean_inc_n(v_a_429_, 2);
v___x_434_ = lean_apply_1(v_inst_427_, v_a_429_);
v___x_435_ = 32ULL;
v___x_436_ = lean_unbox_uint64(v___x_434_);
v___x_437_ = lean_uint64_shift_right(v___x_436_, v___x_435_);
v___x_438_ = lean_unbox_uint64(v___x_434_);
lean_dec_ref(v___x_434_);
v_fold_439_ = lean_uint64_xor(v___x_438_, v___x_437_);
v___x_440_ = 16ULL;
v___x_441_ = lean_uint64_shift_right(v_fold_439_, v___x_440_);
v___x_442_ = lean_uint64_xor(v_fold_439_, v___x_441_);
v___x_443_ = lean_uint64_to_usize(v___x_442_);
v___x_444_ = lean_usize_of_nat(v___x_433_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_sub(v___x_444_, v___x_445_);
v___x_447_ = lean_usize_land(v___x_443_, v___x_446_);
v_bkt_448_ = lean_array_uget_borrowed(v_buckets_432_, v___x_447_);
lean_inc(v_bkt_448_);
lean_inc_ref(v_inst_426_);
v___x_449_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_426_, v_a_429_, v_bkt_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref(v_inst_426_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_apply_1(v_f_430_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_dec(v_a_429_);
lean_dec_ref(v_inst_427_);
return v_m_428_;
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_473_; 
lean_inc_ref(v_buckets_432_);
lean_inc(v_size_431_);
v_isSharedCheck_473_ = !lean_is_exclusive(v_m_428_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; lean_object* v_unused_475_; 
v_unused_474_ = lean_ctor_get(v_m_428_, 1);
lean_dec(v_unused_474_);
v_unused_475_ = lean_ctor_get(v_m_428_, 0);
lean_dec(v_unused_475_);
v___x_453_ = v_m_428_;
v_isShared_454_ = v_isSharedCheck_473_;
goto v_resetjp_452_;
}
else
{
lean_dec(v_m_428_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_473_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_val_455_; lean_object* v___x_456_; lean_object* v_size_x27_457_; lean_object* v___x_458_; lean_object* v_buckets_x27_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_val_455_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v___x_451_, 1);
v___x_456_ = lean_unsigned_to_nat(1u);
v_size_x27_457_ = lean_nat_add(v_size_431_, v___x_456_);
lean_dec(v_size_431_);
lean_inc(v_bkt_448_);
v___x_458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_458_, 0, v_a_429_);
lean_ctor_set(v___x_458_, 1, v_val_455_);
lean_ctor_set(v___x_458_, 2, v_bkt_448_);
v_buckets_x27_459_ = lean_array_uset(v_buckets_432_, v___x_447_, v___x_458_);
v___x_460_ = lean_unsigned_to_nat(4u);
v___x_461_ = lean_nat_mul(v_size_x27_457_, v___x_460_);
v___x_462_ = lean_unsigned_to_nat(3u);
v___x_463_ = lean_nat_div(v___x_461_, v___x_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_array_get_size(v_buckets_x27_459_);
v___x_465_ = lean_nat_dec_le(v___x_463_, v___x_464_);
lean_dec(v___x_463_);
if (v___x_465_ == 0)
{
lean_object* v_val_466_; lean_object* v___x_468_; 
v_val_466_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_427_, v_buckets_x27_459_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v_val_466_);
lean_ctor_set(v___x_453_, 0, v_size_x27_457_);
v___x_468_ = v___x_453_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_size_x27_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_val_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
else
{
lean_object* v___x_471_; 
lean_dec_ref(v_inst_427_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v_buckets_x27_459_);
lean_ctor_set(v___x_453_, 0, v_size_x27_457_);
v___x_471_ = v___x_453_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_size_x27_457_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_buckets_x27_459_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_491_; 
lean_inc(v_bkt_448_);
lean_inc_ref(v_buckets_432_);
lean_inc(v_size_431_);
lean_dec_ref(v_inst_427_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_m_428_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_m_428_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_m_428_, 0);
lean_dec(v_unused_493_);
v___x_477_ = v_m_428_;
v_isShared_478_ = v_isSharedCheck_491_;
goto v_resetjp_476_;
}
else
{
lean_dec(v_m_428_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_491_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v_buckets_x27_480_; lean_object* v_bkt_x27_481_; lean_object* v___y_483_; uint8_t v___x_488_; 
v___x_479_ = lean_box(0);
v_buckets_x27_480_ = lean_array_uset(v_buckets_432_, v___x_447_, v___x_479_);
lean_inc(v_a_429_);
lean_inc_ref(v_inst_426_);
v_bkt_x27_481_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(v_inst_426_, v_a_429_, v_f_430_, v_bkt_448_);
lean_inc(v_bkt_x27_481_);
v___x_488_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_426_, v_a_429_, v_bkt_x27_481_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_sub(v_size_431_, v___x_489_);
lean_dec(v_size_431_);
v___y_483_ = v___x_490_;
goto v___jp_482_;
}
else
{
v___y_483_ = v_size_431_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_array_uset(v_buckets_x27_480_, v___x_447_, v_bkt_x27_481_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v___x_484_);
lean_ctor_set(v___x_477_, 0, v___y_483_);
v___x_486_ = v___x_477_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___y_483_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_m_499_, lean_object* v_a_500_, lean_object* v_f_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_alter___redArg(v_inst_496_, v_inst_497_, v_m_499_, v_a_500_, v_f_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object* v_inst_503_, lean_object* v_inst_504_, lean_object* v_m_505_, lean_object* v_a_506_, lean_object* v_f_507_){
_start:
{
lean_object* v_size_508_; lean_object* v_buckets_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v_fold_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; lean_object* v_bkt_525_; uint8_t v___x_526_; 
v_size_508_ = lean_ctor_get(v_m_505_, 0);
v_buckets_509_ = lean_ctor_get(v_m_505_, 1);
v___x_510_ = lean_array_get_size(v_buckets_509_);
lean_inc_ref(v_inst_504_);
lean_inc_n(v_a_506_, 2);
v___x_511_ = lean_apply_1(v_inst_504_, v_a_506_);
v___x_512_ = 32ULL;
v___x_513_ = lean_unbox_uint64(v___x_511_);
v___x_514_ = lean_uint64_shift_right(v___x_513_, v___x_512_);
v___x_515_ = lean_unbox_uint64(v___x_511_);
lean_dec_ref(v___x_511_);
v_fold_516_ = lean_uint64_xor(v___x_515_, v___x_514_);
v___x_517_ = 16ULL;
v___x_518_ = lean_uint64_shift_right(v_fold_516_, v___x_517_);
v___x_519_ = lean_uint64_xor(v_fold_516_, v___x_518_);
v___x_520_ = lean_uint64_to_usize(v___x_519_);
v___x_521_ = lean_usize_of_nat(v___x_510_);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_sub(v___x_521_, v___x_522_);
v___x_524_ = lean_usize_land(v___x_520_, v___x_523_);
v_bkt_525_ = lean_array_uget_borrowed(v_buckets_509_, v___x_524_);
lean_inc(v_bkt_525_);
lean_inc_ref(v_inst_503_);
v___x_526_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_503_, v_a_506_, v_bkt_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v_inst_503_);
v___x_527_ = lean_box(0);
v___x_528_ = lean_apply_1(v_f_507_, v___x_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_dec(v_a_506_);
lean_dec_ref(v_inst_504_);
return v_m_505_;
}
else
{
lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_550_; 
lean_inc_ref(v_buckets_509_);
lean_inc(v_size_508_);
v_isSharedCheck_550_ = !lean_is_exclusive(v_m_505_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; lean_object* v_unused_552_; 
v_unused_551_ = lean_ctor_get(v_m_505_, 1);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_m_505_, 0);
lean_dec(v_unused_552_);
v___x_530_ = v_m_505_;
v_isShared_531_ = v_isSharedCheck_550_;
goto v_resetjp_529_;
}
else
{
lean_dec(v_m_505_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_550_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v_val_532_; lean_object* v___x_533_; lean_object* v_size_x27_534_; lean_object* v___x_535_; lean_object* v_buckets_x27_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_val_532_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v___x_528_, 1);
v___x_533_ = lean_unsigned_to_nat(1u);
v_size_x27_534_ = lean_nat_add(v_size_508_, v___x_533_);
lean_dec(v_size_508_);
lean_inc(v_bkt_525_);
v___x_535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_535_, 0, v_a_506_);
lean_ctor_set(v___x_535_, 1, v_val_532_);
lean_ctor_set(v___x_535_, 2, v_bkt_525_);
v_buckets_x27_536_ = lean_array_uset(v_buckets_509_, v___x_524_, v___x_535_);
v___x_537_ = lean_unsigned_to_nat(4u);
v___x_538_ = lean_nat_mul(v_size_x27_534_, v___x_537_);
v___x_539_ = lean_unsigned_to_nat(3u);
v___x_540_ = lean_nat_div(v___x_538_, v___x_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_array_get_size(v_buckets_x27_536_);
v___x_542_ = lean_nat_dec_le(v___x_540_, v___x_541_);
lean_dec(v___x_540_);
if (v___x_542_ == 0)
{
lean_object* v_val_543_; lean_object* v___x_545_; 
v_val_543_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_504_, v_buckets_x27_536_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_val_543_);
lean_ctor_set(v___x_530_, 0, v_size_x27_534_);
v___x_545_ = v___x_530_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_size_x27_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_val_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v___x_548_; 
lean_dec_ref(v_inst_504_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v_buckets_x27_536_);
lean_ctor_set(v___x_530_, 0, v_size_x27_534_);
v___x_548_ = v___x_530_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_size_x27_534_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_buckets_x27_536_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
else
{
lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_568_; 
lean_inc(v_bkt_525_);
lean_inc_ref(v_buckets_509_);
lean_inc(v_size_508_);
lean_dec_ref(v_inst_504_);
v_isSharedCheck_568_ = !lean_is_exclusive(v_m_505_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_569_ = lean_ctor_get(v_m_505_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_m_505_, 0);
lean_dec(v_unused_570_);
v___x_554_ = v_m_505_;
v_isShared_555_ = v_isSharedCheck_568_;
goto v_resetjp_553_;
}
else
{
lean_dec(v_m_505_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_568_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v_buckets_x27_557_; lean_object* v_bkt_x27_558_; lean_object* v___y_560_; uint8_t v___x_565_; 
v___x_556_ = lean_box(0);
v_buckets_x27_557_ = lean_array_uset(v_buckets_509_, v___x_524_, v___x_556_);
lean_inc(v_a_506_);
lean_inc_ref(v_inst_503_);
v_bkt_x27_558_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(v_inst_503_, v_a_506_, v_f_507_, v_bkt_525_);
lean_inc(v_bkt_x27_558_);
v___x_565_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_503_, v_a_506_, v_bkt_x27_558_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_sub(v_size_508_, v___x_566_);
lean_dec(v_size_508_);
v___y_560_ = v___x_567_;
goto v___jp_559_;
}
else
{
v___y_560_ = v_size_508_;
goto v___jp_559_;
}
v___jp_559_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_array_uset(v_buckets_x27_557_, v___x_524_, v_bkt_x27_558_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v___x_561_);
lean_ctor_set(v___x_554_, 0, v___y_560_);
v___x_563_ = v___x_554_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___y_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter(lean_object* v_00_u03b1_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_a_576_, lean_object* v_f_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_572_, v_inst_573_, v_m_575_, v_a_576_, v_f_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert___redArg(lean_object* v_inst_579_, lean_object* v_inst_580_, lean_object* v_m_581_, lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_size_584_; lean_object* v_buckets_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_636_; 
v_size_584_ = lean_ctor_get(v_m_581_, 0);
v_buckets_585_ = lean_ctor_get(v_m_581_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_m_581_);
if (v_isSharedCheck_636_ == 0)
{
v___x_587_ = v_m_581_;
v_isShared_588_ = v_isSharedCheck_636_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_buckets_585_);
lean_inc(v_size_584_);
lean_dec(v_m_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_636_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v_fold_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; lean_object* v_bkt_604_; uint8_t v___x_605_; 
v___x_589_ = lean_array_get_size(v_buckets_585_);
lean_inc_ref(v_inst_580_);
lean_inc_n(v_a_582_, 2);
v___x_590_ = lean_apply_1(v_inst_580_, v_a_582_);
v___x_591_ = 32ULL;
v___x_592_ = lean_unbox_uint64(v___x_590_);
v___x_593_ = lean_uint64_shift_right(v___x_592_, v___x_591_);
v___x_594_ = lean_unbox_uint64(v___x_590_);
lean_dec_ref(v___x_590_);
v_fold_595_ = lean_uint64_xor(v___x_594_, v___x_593_);
v___x_596_ = 16ULL;
v___x_597_ = lean_uint64_shift_right(v_fold_595_, v___x_596_);
v___x_598_ = lean_uint64_xor(v_fold_595_, v___x_597_);
v___x_599_ = lean_uint64_to_usize(v___x_598_);
v___x_600_ = lean_usize_of_nat(v___x_589_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_sub(v___x_600_, v___x_601_);
v___x_603_ = lean_usize_land(v___x_599_, v___x_602_);
v_bkt_604_ = lean_array_uget_borrowed(v_buckets_585_, v___x_603_);
lean_inc(v_bkt_604_);
lean_inc_ref(v_inst_579_);
v___x_605_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_579_, v_a_582_, v_bkt_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v_size_x27_607_; lean_object* v___x_608_; lean_object* v_buckets_x27_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
lean_dec_ref(v_inst_579_);
v___x_606_ = lean_unsigned_to_nat(1u);
v_size_x27_607_ = lean_nat_add(v_size_584_, v___x_606_);
lean_dec(v_size_584_);
lean_inc(v_bkt_604_);
v___x_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_608_, 0, v_a_582_);
lean_ctor_set(v___x_608_, 1, v_b_583_);
lean_ctor_set(v___x_608_, 2, v_bkt_604_);
v_buckets_x27_609_ = lean_array_uset(v_buckets_585_, v___x_603_, v___x_608_);
v___x_610_ = lean_unsigned_to_nat(4u);
v___x_611_ = lean_nat_mul(v_size_x27_607_, v___x_610_);
v___x_612_ = lean_unsigned_to_nat(3u);
v___x_613_ = lean_nat_div(v___x_611_, v___x_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_array_get_size(v_buckets_x27_609_);
v___x_615_ = lean_nat_dec_le(v___x_613_, v___x_614_);
lean_dec(v___x_613_);
if (v___x_615_ == 0)
{
lean_object* v_val_616_; lean_object* v___x_618_; 
v_val_616_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_580_, v_buckets_x27_609_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_val_616_);
lean_ctor_set(v___x_587_, 0, v_size_x27_607_);
v___x_618_ = v___x_587_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_size_x27_607_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_val_616_);
v___x_618_ = v_reuseFailAlloc_621_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_box(v___x_605_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
return v___x_620_;
}
}
else
{
lean_object* v___x_623_; 
lean_dec_ref(v_inst_580_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_buckets_x27_609_);
lean_ctor_set(v___x_587_, 0, v_size_x27_607_);
v___x_623_ = v___x_587_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_size_x27_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_buckets_x27_609_);
v___x_623_ = v_reuseFailAlloc_626_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box(v___x_605_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
return v___x_625_;
}
}
}
else
{
lean_object* v___x_627_; lean_object* v_buckets_x27_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_inc(v_bkt_604_);
lean_dec_ref(v_inst_580_);
v___x_627_ = lean_box(0);
v_buckets_x27_628_ = lean_array_uset(v_buckets_585_, v___x_603_, v___x_627_);
v___x_629_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_579_, v_a_582_, v_b_583_, v_bkt_604_);
v___x_630_ = lean_array_uset(v_buckets_x27_628_, v___x_603_, v___x_629_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_630_);
v___x_632_ = v___x_587_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_size_584_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_630_);
v___x_632_ = v_reuseFailAlloc_635_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(v___x_605_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsert(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_inst_639_, lean_object* v_inst_640_, lean_object* v_m_641_, lean_object* v_a_642_, lean_object* v_b_643_){
_start:
{
lean_object* v_size_644_; lean_object* v_buckets_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_696_; 
v_size_644_ = lean_ctor_get(v_m_641_, 0);
v_buckets_645_ = lean_ctor_get(v_m_641_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_m_641_);
if (v_isSharedCheck_696_ == 0)
{
v___x_647_ = v_m_641_;
v_isShared_648_ = v_isSharedCheck_696_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_buckets_645_);
lean_inc(v_size_644_);
lean_dec(v_m_641_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_696_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint64_t v___x_651_; uint64_t v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v_fold_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; size_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v_bkt_664_; uint8_t v___x_665_; 
v___x_649_ = lean_array_get_size(v_buckets_645_);
lean_inc_ref(v_inst_640_);
lean_inc_n(v_a_642_, 2);
v___x_650_ = lean_apply_1(v_inst_640_, v_a_642_);
v___x_651_ = 32ULL;
v___x_652_ = lean_unbox_uint64(v___x_650_);
v___x_653_ = lean_uint64_shift_right(v___x_652_, v___x_651_);
v___x_654_ = lean_unbox_uint64(v___x_650_);
lean_dec_ref(v___x_650_);
v_fold_655_ = lean_uint64_xor(v___x_654_, v___x_653_);
v___x_656_ = 16ULL;
v___x_657_ = lean_uint64_shift_right(v_fold_655_, v___x_656_);
v___x_658_ = lean_uint64_xor(v_fold_655_, v___x_657_);
v___x_659_ = lean_uint64_to_usize(v___x_658_);
v___x_660_ = lean_usize_of_nat(v___x_649_);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_sub(v___x_660_, v___x_661_);
v___x_663_ = lean_usize_land(v___x_659_, v___x_662_);
v_bkt_664_ = lean_array_uget_borrowed(v_buckets_645_, v___x_663_);
lean_inc(v_bkt_664_);
lean_inc_ref(v_inst_639_);
v___x_665_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_639_, v_a_642_, v_bkt_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v_size_x27_667_; lean_object* v___x_668_; lean_object* v_buckets_x27_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
lean_dec_ref(v_inst_639_);
v___x_666_ = lean_unsigned_to_nat(1u);
v_size_x27_667_ = lean_nat_add(v_size_644_, v___x_666_);
lean_dec(v_size_644_);
lean_inc(v_bkt_664_);
v___x_668_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_668_, 0, v_a_642_);
lean_ctor_set(v___x_668_, 1, v_b_643_);
lean_ctor_set(v___x_668_, 2, v_bkt_664_);
v_buckets_x27_669_ = lean_array_uset(v_buckets_645_, v___x_663_, v___x_668_);
v___x_670_ = lean_unsigned_to_nat(4u);
v___x_671_ = lean_nat_mul(v_size_x27_667_, v___x_670_);
v___x_672_ = lean_unsigned_to_nat(3u);
v___x_673_ = lean_nat_div(v___x_671_, v___x_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_array_get_size(v_buckets_x27_669_);
v___x_675_ = lean_nat_dec_le(v___x_673_, v___x_674_);
lean_dec(v___x_673_);
if (v___x_675_ == 0)
{
lean_object* v_val_676_; lean_object* v___x_678_; 
v_val_676_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_640_, v_buckets_x27_669_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_val_676_);
lean_ctor_set(v___x_647_, 0, v_size_x27_667_);
v___x_678_ = v___x_647_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_size_x27_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_val_676_);
v___x_678_ = v_reuseFailAlloc_681_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(v___x_665_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
return v___x_680_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v_inst_640_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_buckets_x27_669_);
lean_ctor_set(v___x_647_, 0, v_size_x27_667_);
v___x_683_ = v___x_647_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_size_x27_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_buckets_x27_669_);
v___x_683_ = v_reuseFailAlloc_686_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_box(v___x_665_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
return v___x_685_;
}
}
}
else
{
lean_object* v___x_687_; lean_object* v_buckets_x27_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
lean_inc(v_bkt_664_);
lean_dec_ref(v_inst_640_);
v___x_687_ = lean_box(0);
v_buckets_x27_688_ = lean_array_uset(v_buckets_645_, v___x_663_, v___x_687_);
v___x_689_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_639_, v_a_642_, v_b_643_, v_bkt_664_);
v___x_690_ = lean_array_uset(v_buckets_x27_688_, v___x_663_, v___x_689_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_690_);
v___x_692_ = v___x_647_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_size_644_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_695_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(v___x_665_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew___redArg(lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_m_699_, lean_object* v_a_700_, lean_object* v_b_701_){
_start:
{
lean_object* v_size_702_; lean_object* v_buckets_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v_fold_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; lean_object* v_bkt_719_; uint8_t v___x_720_; 
v_size_702_ = lean_ctor_get(v_m_699_, 0);
v_buckets_703_ = lean_ctor_get(v_m_699_, 1);
v___x_704_ = lean_array_get_size(v_buckets_703_);
lean_inc_ref(v_inst_698_);
lean_inc_n(v_a_700_, 2);
v___x_705_ = lean_apply_1(v_inst_698_, v_a_700_);
v___x_706_ = 32ULL;
v___x_707_ = lean_unbox_uint64(v___x_705_);
v___x_708_ = lean_uint64_shift_right(v___x_707_, v___x_706_);
v___x_709_ = lean_unbox_uint64(v___x_705_);
lean_dec_ref(v___x_705_);
v_fold_710_ = lean_uint64_xor(v___x_709_, v___x_708_);
v___x_711_ = 16ULL;
v___x_712_ = lean_uint64_shift_right(v_fold_710_, v___x_711_);
v___x_713_ = lean_uint64_xor(v_fold_710_, v___x_712_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
v___x_715_ = lean_usize_of_nat(v___x_704_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_sub(v___x_715_, v___x_716_);
v___x_718_ = lean_usize_land(v___x_714_, v___x_717_);
v_bkt_719_ = lean_array_uget_borrowed(v_buckets_703_, v___x_718_);
lean_inc(v_bkt_719_);
v___x_720_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_697_, v_a_700_, v_bkt_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_745_; 
lean_inc_ref(v_buckets_703_);
lean_inc(v_size_702_);
v_isSharedCheck_745_ = !lean_is_exclusive(v_m_699_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; lean_object* v_unused_747_; 
v_unused_746_ = lean_ctor_get(v_m_699_, 1);
lean_dec(v_unused_746_);
v_unused_747_ = lean_ctor_get(v_m_699_, 0);
lean_dec(v_unused_747_);
v___x_722_ = v_m_699_;
v_isShared_723_ = v_isSharedCheck_745_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_m_699_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_745_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v_size_x27_725_; lean_object* v___x_726_; lean_object* v_buckets_x27_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v_size_x27_725_ = lean_nat_add(v_size_702_, v___x_724_);
lean_dec(v_size_702_);
lean_inc(v_bkt_719_);
v___x_726_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_726_, 0, v_a_700_);
lean_ctor_set(v___x_726_, 1, v_b_701_);
lean_ctor_set(v___x_726_, 2, v_bkt_719_);
v_buckets_x27_727_ = lean_array_uset(v_buckets_703_, v___x_718_, v___x_726_);
v___x_728_ = lean_unsigned_to_nat(4u);
v___x_729_ = lean_nat_mul(v_size_x27_725_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(3u);
v___x_731_ = lean_nat_div(v___x_729_, v___x_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_array_get_size(v_buckets_x27_727_);
v___x_733_ = lean_nat_dec_le(v___x_731_, v___x_732_);
lean_dec(v___x_731_);
if (v___x_733_ == 0)
{
lean_object* v_val_734_; lean_object* v___x_736_; 
v_val_734_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_698_, v_buckets_x27_727_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_val_734_);
lean_ctor_set(v___x_722_, 0, v_size_x27_725_);
v___x_736_ = v___x_722_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_x27_725_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_val_734_);
v___x_736_ = v_reuseFailAlloc_739_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_box(v___x_720_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
return v___x_738_;
}
}
else
{
lean_object* v___x_741_; 
lean_dec_ref(v_inst_698_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v_buckets_x27_727_);
lean_ctor_set(v___x_722_, 0, v_size_x27_725_);
v___x_741_ = v___x_722_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_size_x27_725_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_buckets_x27_727_);
v___x_741_ = v_reuseFailAlloc_744_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_box(v___x_720_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
return v___x_743_;
}
}
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_b_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_inst_698_);
v___x_748_ = lean_box(v___x_720_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_m_699_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_containsThenInsertIfNew(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_m_754_, lean_object* v_a_755_, lean_object* v_b_756_){
_start:
{
lean_object* v_size_757_; lean_object* v_buckets_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v_fold_765_; uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v___x_768_; size_t v___x_769_; size_t v___x_770_; size_t v___x_771_; size_t v___x_772_; size_t v___x_773_; lean_object* v_bkt_774_; uint8_t v___x_775_; 
v_size_757_ = lean_ctor_get(v_m_754_, 0);
v_buckets_758_ = lean_ctor_get(v_m_754_, 1);
v___x_759_ = lean_array_get_size(v_buckets_758_);
lean_inc_ref(v_inst_753_);
lean_inc_n(v_a_755_, 2);
v___x_760_ = lean_apply_1(v_inst_753_, v_a_755_);
v___x_761_ = 32ULL;
v___x_762_ = lean_unbox_uint64(v___x_760_);
v___x_763_ = lean_uint64_shift_right(v___x_762_, v___x_761_);
v___x_764_ = lean_unbox_uint64(v___x_760_);
lean_dec_ref(v___x_760_);
v_fold_765_ = lean_uint64_xor(v___x_764_, v___x_763_);
v___x_766_ = 16ULL;
v___x_767_ = lean_uint64_shift_right(v_fold_765_, v___x_766_);
v___x_768_ = lean_uint64_xor(v_fold_765_, v___x_767_);
v___x_769_ = lean_uint64_to_usize(v___x_768_);
v___x_770_ = lean_usize_of_nat(v___x_759_);
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_sub(v___x_770_, v___x_771_);
v___x_773_ = lean_usize_land(v___x_769_, v___x_772_);
v_bkt_774_ = lean_array_uget_borrowed(v_buckets_758_, v___x_773_);
lean_inc(v_bkt_774_);
v___x_775_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_752_, v_a_755_, v_bkt_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_800_; 
lean_inc_ref(v_buckets_758_);
lean_inc(v_size_757_);
v_isSharedCheck_800_ = !lean_is_exclusive(v_m_754_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; lean_object* v_unused_802_; 
v_unused_801_ = lean_ctor_get(v_m_754_, 1);
lean_dec(v_unused_801_);
v_unused_802_ = lean_ctor_get(v_m_754_, 0);
lean_dec(v_unused_802_);
v___x_777_ = v_m_754_;
v_isShared_778_ = v_isSharedCheck_800_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_m_754_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_800_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v_size_x27_780_; lean_object* v___x_781_; lean_object* v_buckets_x27_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_779_ = lean_unsigned_to_nat(1u);
v_size_x27_780_ = lean_nat_add(v_size_757_, v___x_779_);
lean_dec(v_size_757_);
lean_inc(v_bkt_774_);
v___x_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_781_, 0, v_a_755_);
lean_ctor_set(v___x_781_, 1, v_b_756_);
lean_ctor_set(v___x_781_, 2, v_bkt_774_);
v_buckets_x27_782_ = lean_array_uset(v_buckets_758_, v___x_773_, v___x_781_);
v___x_783_ = lean_unsigned_to_nat(4u);
v___x_784_ = lean_nat_mul(v_size_x27_780_, v___x_783_);
v___x_785_ = lean_unsigned_to_nat(3u);
v___x_786_ = lean_nat_div(v___x_784_, v___x_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_array_get_size(v_buckets_x27_782_);
v___x_788_ = lean_nat_dec_le(v___x_786_, v___x_787_);
lean_dec(v___x_786_);
if (v___x_788_ == 0)
{
lean_object* v_val_789_; lean_object* v___x_791_; 
v_val_789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_753_, v_buckets_x27_782_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_val_789_);
lean_ctor_set(v___x_777_, 0, v_size_x27_780_);
v___x_791_ = v___x_777_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_size_x27_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_val_789_);
v___x_791_ = v_reuseFailAlloc_794_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_box(v___x_775_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
return v___x_793_;
}
}
else
{
lean_object* v___x_796_; 
lean_dec_ref(v_inst_753_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_buckets_x27_782_);
lean_ctor_set(v___x_777_, 0, v_size_x27_780_);
v___x_796_ = v___x_777_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_size_x27_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_buckets_x27_782_);
v___x_796_ = v_reuseFailAlloc_799_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_box(v___x_775_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
return v___x_798_;
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v_b_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_inst_753_);
v___x_803_ = lean_box(v___x_775_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_m_754_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_m_807_, lean_object* v_a_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_size_810_; lean_object* v_buckets_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; uint64_t v___x_816_; uint64_t v___x_817_; uint64_t v_fold_818_; uint64_t v___x_819_; uint64_t v___x_820_; uint64_t v___x_821_; size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v_bkt_827_; uint8_t v___x_828_; 
v_size_810_ = lean_ctor_get(v_m_807_, 0);
v_buckets_811_ = lean_ctor_get(v_m_807_, 1);
v___x_812_ = lean_array_get_size(v_buckets_811_);
lean_inc_ref(v_inst_806_);
lean_inc_n(v_a_808_, 2);
v___x_813_ = lean_apply_1(v_inst_806_, v_a_808_);
v___x_814_ = 32ULL;
v___x_815_ = lean_unbox_uint64(v___x_813_);
v___x_816_ = lean_uint64_shift_right(v___x_815_, v___x_814_);
v___x_817_ = lean_unbox_uint64(v___x_813_);
lean_dec_ref(v___x_813_);
v_fold_818_ = lean_uint64_xor(v___x_817_, v___x_816_);
v___x_819_ = 16ULL;
v___x_820_ = lean_uint64_shift_right(v_fold_818_, v___x_819_);
v___x_821_ = lean_uint64_xor(v_fold_818_, v___x_820_);
v___x_822_ = lean_uint64_to_usize(v___x_821_);
v___x_823_ = lean_usize_of_nat(v___x_812_);
v___x_824_ = ((size_t)1ULL);
v___x_825_ = lean_usize_sub(v___x_823_, v___x_824_);
v___x_826_ = lean_usize_land(v___x_822_, v___x_825_);
v_bkt_827_ = lean_array_uget_borrowed(v_buckets_811_, v___x_826_);
lean_inc(v_bkt_827_);
v___x_828_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_805_, v_a_808_, v_bkt_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_849_; 
lean_inc_ref(v_buckets_811_);
lean_inc(v_size_810_);
v_isSharedCheck_849_ = !lean_is_exclusive(v_m_807_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_850_ = lean_ctor_get(v_m_807_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v_m_807_, 0);
lean_dec(v_unused_851_);
v___x_830_ = v_m_807_;
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
else
{
lean_dec(v_m_807_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v_size_x27_833_; lean_object* v___x_834_; lean_object* v_buckets_x27_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v_size_x27_833_ = lean_nat_add(v_size_810_, v___x_832_);
lean_dec(v_size_810_);
lean_inc(v_bkt_827_);
v___x_834_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_834_, 0, v_a_808_);
lean_ctor_set(v___x_834_, 1, v_b_809_);
lean_ctor_set(v___x_834_, 2, v_bkt_827_);
v_buckets_x27_835_ = lean_array_uset(v_buckets_811_, v___x_826_, v___x_834_);
v___x_836_ = lean_unsigned_to_nat(4u);
v___x_837_ = lean_nat_mul(v_size_x27_833_, v___x_836_);
v___x_838_ = lean_unsigned_to_nat(3u);
v___x_839_ = lean_nat_div(v___x_837_, v___x_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_array_get_size(v_buckets_x27_835_);
v___x_841_ = lean_nat_dec_le(v___x_839_, v___x_840_);
lean_dec(v___x_839_);
if (v___x_841_ == 0)
{
lean_object* v_val_842_; lean_object* v___x_844_; 
v_val_842_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_806_, v_buckets_x27_835_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v_val_842_);
lean_ctor_set(v___x_830_, 0, v_size_x27_833_);
v___x_844_ = v___x_830_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_size_x27_833_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_val_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_847_; 
lean_dec_ref(v_inst_806_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 1, v_buckets_x27_835_);
lean_ctor_set(v___x_830_, 0, v_size_x27_833_);
v___x_847_ = v___x_830_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_size_x27_833_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_buckets_x27_835_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_dec(v_b_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_inst_806_);
return v_m_807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew(lean_object* v_00_u03b1_852_, lean_object* v_00_u03b2_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_m_856_, lean_object* v_a_857_, lean_object* v_b_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_854_, v_inst_855_, v_m_856_, v_a_857_, v_b_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_m_862_, lean_object* v_a_863_, lean_object* v_b_864_){
_start:
{
lean_object* v_size_865_; lean_object* v_buckets_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; uint64_t v___x_871_; uint64_t v___x_872_; uint64_t v_fold_873_; uint64_t v___x_874_; uint64_t v___x_875_; uint64_t v___x_876_; size_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v_bkt_882_; lean_object* v___x_883_; 
v_size_865_ = lean_ctor_get(v_m_862_, 0);
v_buckets_866_ = lean_ctor_get(v_m_862_, 1);
v___x_867_ = lean_array_get_size(v_buckets_866_);
lean_inc_ref(v_inst_861_);
lean_inc_n(v_a_863_, 2);
v___x_868_ = lean_apply_1(v_inst_861_, v_a_863_);
v___x_869_ = 32ULL;
v___x_870_ = lean_unbox_uint64(v___x_868_);
v___x_871_ = lean_uint64_shift_right(v___x_870_, v___x_869_);
v___x_872_ = lean_unbox_uint64(v___x_868_);
lean_dec_ref(v___x_868_);
v_fold_873_ = lean_uint64_xor(v___x_872_, v___x_871_);
v___x_874_ = 16ULL;
v___x_875_ = lean_uint64_shift_right(v_fold_873_, v___x_874_);
v___x_876_ = lean_uint64_xor(v_fold_873_, v___x_875_);
v___x_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = lean_usize_of_nat(v___x_867_);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_sub(v___x_878_, v___x_879_);
v___x_881_ = lean_usize_land(v___x_877_, v___x_880_);
v_bkt_882_ = lean_array_uget_borrowed(v_buckets_866_, v___x_881_);
lean_inc(v_bkt_882_);
v___x_883_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_860_, v_a_863_, v_bkt_882_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_906_; 
lean_inc_ref(v_buckets_866_);
lean_inc(v_size_865_);
v_isSharedCheck_906_ = !lean_is_exclusive(v_m_862_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_907_ = lean_ctor_get(v_m_862_, 1);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_m_862_, 0);
lean_dec(v_unused_908_);
v___x_885_ = v_m_862_;
v_isShared_886_ = v_isSharedCheck_906_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_m_862_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_906_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v_size_x27_888_; lean_object* v___x_889_; lean_object* v_buckets_x27_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_887_ = lean_unsigned_to_nat(1u);
v_size_x27_888_ = lean_nat_add(v_size_865_, v___x_887_);
lean_dec(v_size_865_);
lean_inc(v_bkt_882_);
v___x_889_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_889_, 0, v_a_863_);
lean_ctor_set(v___x_889_, 1, v_b_864_);
lean_ctor_set(v___x_889_, 2, v_bkt_882_);
v_buckets_x27_890_ = lean_array_uset(v_buckets_866_, v___x_881_, v___x_889_);
v___x_891_ = lean_unsigned_to_nat(4u);
v___x_892_ = lean_nat_mul(v_size_x27_888_, v___x_891_);
v___x_893_ = lean_unsigned_to_nat(3u);
v___x_894_ = lean_nat_div(v___x_892_, v___x_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_array_get_size(v_buckets_x27_890_);
v___x_896_ = lean_nat_dec_le(v___x_894_, v___x_895_);
lean_dec(v___x_894_);
if (v___x_896_ == 0)
{
lean_object* v_val_897_; lean_object* v___x_899_; 
v_val_897_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_861_, v_buckets_x27_890_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v_val_897_);
lean_ctor_set(v___x_885_, 0, v_size_x27_888_);
v___x_899_ = v___x_885_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_size_x27_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_val_897_);
v___x_899_ = v_reuseFailAlloc_901_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_883_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
return v___x_900_;
}
}
else
{
lean_object* v___x_903_; 
lean_dec_ref(v_inst_861_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v_buckets_x27_890_);
lean_ctor_set(v___x_885_, 0, v_size_x27_888_);
v___x_903_ = v___x_885_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_size_x27_888_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_buckets_x27_890_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_883_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
return v___x_904_;
}
}
}
}
else
{
lean_object* v___x_909_; 
lean_dec(v_b_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_inst_861_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_883_);
lean_ctor_set(v___x_909_, 1, v_m_862_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_m_915_, lean_object* v_a_916_, lean_object* v_b_917_){
_start:
{
lean_object* v_size_918_; lean_object* v_buckets_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; uint64_t v___x_924_; uint64_t v___x_925_; uint64_t v_fold_926_; uint64_t v___x_927_; uint64_t v___x_928_; uint64_t v___x_929_; size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; size_t v___x_934_; lean_object* v_bkt_935_; lean_object* v___x_936_; 
v_size_918_ = lean_ctor_get(v_m_915_, 0);
v_buckets_919_ = lean_ctor_get(v_m_915_, 1);
v___x_920_ = lean_array_get_size(v_buckets_919_);
lean_inc_ref(v_inst_913_);
lean_inc_n(v_a_916_, 2);
v___x_921_ = lean_apply_1(v_inst_913_, v_a_916_);
v___x_922_ = 32ULL;
v___x_923_ = lean_unbox_uint64(v___x_921_);
v___x_924_ = lean_uint64_shift_right(v___x_923_, v___x_922_);
v___x_925_ = lean_unbox_uint64(v___x_921_);
lean_dec_ref(v___x_921_);
v_fold_926_ = lean_uint64_xor(v___x_925_, v___x_924_);
v___x_927_ = 16ULL;
v___x_928_ = lean_uint64_shift_right(v_fold_926_, v___x_927_);
v___x_929_ = lean_uint64_xor(v_fold_926_, v___x_928_);
v___x_930_ = lean_uint64_to_usize(v___x_929_);
v___x_931_ = lean_usize_of_nat(v___x_920_);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_sub(v___x_931_, v___x_932_);
v___x_934_ = lean_usize_land(v___x_930_, v___x_933_);
v_bkt_935_ = lean_array_uget_borrowed(v_buckets_919_, v___x_934_);
lean_inc(v_bkt_935_);
v___x_936_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_912_, v_a_916_, v_bkt_935_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_959_; 
lean_inc_ref(v_buckets_919_);
lean_inc(v_size_918_);
v_isSharedCheck_959_ = !lean_is_exclusive(v_m_915_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; lean_object* v_unused_961_; 
v_unused_960_ = lean_ctor_get(v_m_915_, 1);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_m_915_, 0);
lean_dec(v_unused_961_);
v___x_938_ = v_m_915_;
v_isShared_939_ = v_isSharedCheck_959_;
goto v_resetjp_937_;
}
else
{
lean_dec(v_m_915_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_959_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v_size_x27_941_; lean_object* v___x_942_; lean_object* v_buckets_x27_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_940_ = lean_unsigned_to_nat(1u);
v_size_x27_941_ = lean_nat_add(v_size_918_, v___x_940_);
lean_dec(v_size_918_);
lean_inc(v_bkt_935_);
v___x_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_942_, 0, v_a_916_);
lean_ctor_set(v___x_942_, 1, v_b_917_);
lean_ctor_set(v___x_942_, 2, v_bkt_935_);
v_buckets_x27_943_ = lean_array_uset(v_buckets_919_, v___x_934_, v___x_942_);
v___x_944_ = lean_unsigned_to_nat(4u);
v___x_945_ = lean_nat_mul(v_size_x27_941_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(3u);
v___x_947_ = lean_nat_div(v___x_945_, v___x_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_array_get_size(v_buckets_x27_943_);
v___x_949_ = lean_nat_dec_le(v___x_947_, v___x_948_);
lean_dec(v___x_947_);
if (v___x_949_ == 0)
{
lean_object* v_val_950_; lean_object* v___x_952_; 
v_val_950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_913_, v_buckets_x27_943_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_val_950_);
lean_ctor_set(v___x_938_, 0, v_size_x27_941_);
v___x_952_ = v___x_938_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_size_x27_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_val_950_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_953_; 
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_936_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; 
lean_dec_ref(v_inst_913_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_buckets_x27_943_);
lean_ctor_set(v___x_938_, 0, v_size_x27_941_);
v___x_956_ = v___x_938_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_size_x27_941_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_buckets_x27_943_);
v___x_956_ = v_reuseFailAlloc_958_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_936_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v_b_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_inst_913_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_936_);
lean_ctor_set(v___x_962_, 1, v_m_915_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_m_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_buckets_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint64_t v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v_fold_974_; uint64_t v___x_975_; uint64_t v___x_976_; uint64_t v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_buckets_967_ = lean_ctor_get(v_m_965_, 1);
v___x_968_ = lean_array_get_size(v_buckets_967_);
lean_inc(v_a_966_);
v___x_969_ = lean_apply_1(v_inst_964_, v_a_966_);
v___x_970_ = 32ULL;
v___x_971_ = lean_unbox_uint64(v___x_969_);
v___x_972_ = lean_uint64_shift_right(v___x_971_, v___x_970_);
v___x_973_ = lean_unbox_uint64(v___x_969_);
lean_dec_ref(v___x_969_);
v_fold_974_ = lean_uint64_xor(v___x_973_, v___x_972_);
v___x_975_ = 16ULL;
v___x_976_ = lean_uint64_shift_right(v_fold_974_, v___x_975_);
v___x_977_ = lean_uint64_xor(v_fold_974_, v___x_976_);
v___x_978_ = lean_uint64_to_usize(v___x_977_);
v___x_979_ = lean_usize_of_nat(v___x_968_);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_sub(v___x_979_, v___x_980_);
v___x_982_ = lean_usize_land(v___x_978_, v___x_981_);
v___x_983_ = lean_array_uget_borrowed(v_buckets_967_, v___x_982_);
lean_inc(v___x_983_);
v___x_984_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_963_, v_a_966_, v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg___boxed(lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_m_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_985_, v_inst_986_, v_m_987_, v_a_988_);
lean_dec_ref(v_m_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_m_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_992_, v_inst_994_, v_m_995_, v_a_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___boxed(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_inst_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_m_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f(v_00_u03b1_998_, v_00_u03b2_999_, v_inst_1000_, v_inst_1001_, v_inst_1002_, v_m_1003_, v_a_1004_);
lean_dec_ref(v_m_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_m_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_buckets_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v_fold_1017_; uint64_t v___x_1018_; uint64_t v___x_1019_; uint64_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_buckets_1010_ = lean_ctor_get(v_m_1008_, 1);
v___x_1011_ = lean_array_get_size(v_buckets_1010_);
lean_inc(v_a_1009_);
v___x_1012_ = lean_apply_1(v_inst_1007_, v_a_1009_);
v___x_1013_ = 32ULL;
v___x_1014_ = lean_unbox_uint64(v___x_1012_);
v___x_1015_ = lean_uint64_shift_right(v___x_1014_, v___x_1013_);
v___x_1016_ = lean_unbox_uint64(v___x_1012_);
lean_dec_ref(v___x_1012_);
v_fold_1017_ = lean_uint64_xor(v___x_1016_, v___x_1015_);
v___x_1018_ = 16ULL;
v___x_1019_ = lean_uint64_shift_right(v_fold_1017_, v___x_1018_);
v___x_1020_ = lean_uint64_xor(v_fold_1017_, v___x_1019_);
v___x_1021_ = lean_uint64_to_usize(v___x_1020_);
v___x_1022_ = lean_usize_of_nat(v___x_1011_);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_sub(v___x_1022_, v___x_1023_);
v___x_1025_ = lean_usize_land(v___x_1021_, v___x_1024_);
v___x_1026_ = lean_array_uget_borrowed(v_buckets_1010_, v___x_1025_);
lean_inc(v___x_1026_);
v___x_1027_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1006_, v_a_1009_, v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___redArg___boxed(lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_m_1030_, lean_object* v_a_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1028_, v_inst_1029_, v_m_1030_, v_a_1031_);
lean_dec_ref(v_m_1030_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1036_, v_inst_1037_, v_m_1038_, v_a_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_m_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_res_1047_; lean_object* v_r_1048_; 
v_res_1047_ = l_Std_DHashMap_Internal_Raw_u2080_contains(v_00_u03b1_1041_, v_00_u03b2_1042_, v_inst_1043_, v_inst_1044_, v_m_1045_, v_a_1046_);
lean_dec_ref(v_m_1045_);
v_r_1048_ = lean_box(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg(lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_m_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_buckets_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v___x_1059_; uint64_t v_fold_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_buckets_1053_ = lean_ctor_get(v_m_1051_, 1);
v___x_1054_ = lean_array_get_size(v_buckets_1053_);
lean_inc(v_a_1052_);
v___x_1055_ = lean_apply_1(v_inst_1050_, v_a_1052_);
v___x_1056_ = 32ULL;
v___x_1057_ = lean_unbox_uint64(v___x_1055_);
v___x_1058_ = lean_uint64_shift_right(v___x_1057_, v___x_1056_);
v___x_1059_ = lean_unbox_uint64(v___x_1055_);
lean_dec_ref(v___x_1055_);
v_fold_1060_ = lean_uint64_xor(v___x_1059_, v___x_1058_);
v___x_1061_ = 16ULL;
v___x_1062_ = lean_uint64_shift_right(v_fold_1060_, v___x_1061_);
v___x_1063_ = lean_uint64_xor(v_fold_1060_, v___x_1062_);
v___x_1064_ = lean_uint64_to_usize(v___x_1063_);
v___x_1065_ = lean_usize_of_nat(v___x_1054_);
v___x_1066_ = ((size_t)1ULL);
v___x_1067_ = lean_usize_sub(v___x_1065_, v___x_1066_);
v___x_1068_ = lean_usize_land(v___x_1064_, v___x_1067_);
v___x_1069_ = lean_array_uget_borrowed(v_buckets_1053_, v___x_1068_);
lean_inc(v___x_1069_);
v___x_1070_ = l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_1049_, v_a_1052_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___redArg___boxed(lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_m_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_1071_, v_inst_1072_, v_m_1073_, v_a_1074_);
lean_dec_ref(v_m_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_m_1081_, lean_object* v_a_1082_, lean_object* v_hma_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_get___redArg(v_inst_1078_, v_inst_1080_, v_m_1081_, v_a_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get___boxed(lean_object* v_00_u03b1_1085_, lean_object* v_00_u03b2_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_m_1090_, lean_object* v_a_1091_, lean_object* v_hma_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DHashMap_Internal_Raw_u2080_get(v_00_u03b1_1085_, v_00_u03b2_1086_, v_inst_1087_, v_inst_1088_, v_inst_1089_, v_m_1090_, v_a_1091_, v_hma_1092_);
lean_dec_ref(v_m_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_m_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_buckets_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v___x_1104_; uint64_t v_fold_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; uint64_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; size_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_buckets_1098_ = lean_ctor_get(v_m_1096_, 1);
v___x_1099_ = lean_array_get_size(v_buckets_1098_);
lean_inc(v_a_1097_);
v___x_1100_ = lean_apply_1(v_inst_1095_, v_a_1097_);
v___x_1101_ = 32ULL;
v___x_1102_ = lean_unbox_uint64(v___x_1100_);
v___x_1103_ = lean_uint64_shift_right(v___x_1102_, v___x_1101_);
v___x_1104_ = lean_unbox_uint64(v___x_1100_);
lean_dec_ref(v___x_1100_);
v_fold_1105_ = lean_uint64_xor(v___x_1104_, v___x_1103_);
v___x_1106_ = 16ULL;
v___x_1107_ = lean_uint64_shift_right(v_fold_1105_, v___x_1106_);
v___x_1108_ = lean_uint64_xor(v_fold_1105_, v___x_1107_);
v___x_1109_ = lean_uint64_to_usize(v___x_1108_);
v___x_1110_ = lean_usize_of_nat(v___x_1099_);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = lean_usize_sub(v___x_1110_, v___x_1111_);
v___x_1113_ = lean_usize_land(v___x_1109_, v___x_1112_);
v___x_1114_ = lean_array_uget_borrowed(v_buckets_1098_, v___x_1113_);
lean_inc(v___x_1114_);
v___x_1115_ = l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_1094_, v_a_1097_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg___boxed(lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_m_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1116_, v_inst_1117_, v_m_1118_, v_a_1119_);
lean_dec_ref(v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry(lean_object* v_00_u03b1_1121_, lean_object* v_00_u03b2_1122_, lean_object* v_inst_1123_, lean_object* v_inst_1124_, lean_object* v_m_1125_, lean_object* v_a_1126_, lean_object* v_hma_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1123_, v_inst_1124_, v_m_1125_, v_a_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_m_1133_, lean_object* v_a_1134_, lean_object* v_hma_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry(v_00_u03b1_1129_, v_00_u03b2_1130_, v_inst_1131_, v_inst_1132_, v_m_1133_, v_a_1134_, v_hma_1135_);
lean_dec_ref(v_m_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_buckets_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint64_t v___x_1144_; uint64_t v___x_1145_; uint64_t v___x_1146_; uint64_t v___x_1147_; uint64_t v_fold_1148_; uint64_t v___x_1149_; uint64_t v___x_1150_; uint64_t v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_buckets_1141_ = lean_ctor_get(v_m_1139_, 1);
v___x_1142_ = lean_array_get_size(v_buckets_1141_);
lean_inc(v_a_1140_);
v___x_1143_ = lean_apply_1(v_inst_1138_, v_a_1140_);
v___x_1144_ = 32ULL;
v___x_1145_ = lean_unbox_uint64(v___x_1143_);
v___x_1146_ = lean_uint64_shift_right(v___x_1145_, v___x_1144_);
v___x_1147_ = lean_unbox_uint64(v___x_1143_);
lean_dec_ref(v___x_1143_);
v_fold_1148_ = lean_uint64_xor(v___x_1147_, v___x_1146_);
v___x_1149_ = 16ULL;
v___x_1150_ = lean_uint64_shift_right(v_fold_1148_, v___x_1149_);
v___x_1151_ = lean_uint64_xor(v_fold_1148_, v___x_1150_);
v___x_1152_ = lean_uint64_to_usize(v___x_1151_);
v___x_1153_ = lean_usize_of_nat(v___x_1142_);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_sub(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_usize_land(v___x_1152_, v___x_1155_);
v___x_1157_ = lean_array_uget_borrowed(v_buckets_1141_, v___x_1156_);
lean_inc(v___x_1157_);
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_1137_, v_a_1140_, v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg___boxed(lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1159_, v_inst_1160_, v_m_1161_, v_a_1162_);
lean_dec_ref(v_m_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1166_, v_inst_1167_, v_m_1168_, v_a_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_m_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f(v_00_u03b1_1171_, v_00_u03b2_1172_, v_inst_1173_, v_inst_1174_, v_m_1175_, v_a_1176_);
lean_dec_ref(v_m_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_m_1180_, lean_object* v_a_1181_, lean_object* v_fallback_1182_){
_start:
{
lean_object* v_buckets_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; uint64_t v___x_1189_; uint64_t v_fold_1190_; uint64_t v___x_1191_; uint64_t v___x_1192_; uint64_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; size_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_buckets_1183_ = lean_ctor_get(v_m_1180_, 1);
v___x_1184_ = lean_array_get_size(v_buckets_1183_);
lean_inc(v_a_1181_);
v___x_1185_ = lean_apply_1(v_inst_1179_, v_a_1181_);
v___x_1186_ = 32ULL;
v___x_1187_ = lean_unbox_uint64(v___x_1185_);
v___x_1188_ = lean_uint64_shift_right(v___x_1187_, v___x_1186_);
v___x_1189_ = lean_unbox_uint64(v___x_1185_);
lean_dec_ref(v___x_1185_);
v_fold_1190_ = lean_uint64_xor(v___x_1189_, v___x_1188_);
v___x_1191_ = 16ULL;
v___x_1192_ = lean_uint64_shift_right(v_fold_1190_, v___x_1191_);
v___x_1193_ = lean_uint64_xor(v_fold_1190_, v___x_1192_);
v___x_1194_ = lean_uint64_to_usize(v___x_1193_);
v___x_1195_ = lean_usize_of_nat(v___x_1184_);
v___x_1196_ = ((size_t)1ULL);
v___x_1197_ = lean_usize_sub(v___x_1195_, v___x_1196_);
v___x_1198_ = lean_usize_land(v___x_1194_, v___x_1197_);
v___x_1199_ = lean_array_uget_borrowed(v_buckets_1183_, v___x_1198_);
lean_inc(v___x_1199_);
v___x_1200_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(v_inst_1178_, v_a_1181_, v_fallback_1182_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg___boxed(lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_m_1203_, lean_object* v_a_1204_, lean_object* v_fallback_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1201_, v_inst_1202_, v_m_1203_, v_a_1204_, v_fallback_1205_);
lean_dec_ref(v_fallback_1205_);
lean_dec_ref(v_m_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD(lean_object* v_00_u03b1_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_m_1211_, lean_object* v_a_1212_, lean_object* v_fallback_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1209_, v_inst_1210_, v_m_1211_, v_a_1212_, v_fallback_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___boxed(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_m_1219_, lean_object* v_a_1220_, lean_object* v_fallback_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD(v_00_u03b1_1215_, v_00_u03b2_1216_, v_inst_1217_, v_inst_1218_, v_m_1219_, v_a_1220_, v_fallback_1221_);
lean_dec_ref(v_fallback_1221_);
lean_dec_ref(v_m_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_m_1225_, lean_object* v_a_1226_, lean_object* v_inst_1227_){
_start:
{
lean_object* v_buckets_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint64_t v___x_1231_; uint64_t v___x_1232_; uint64_t v___x_1233_; uint64_t v___x_1234_; uint64_t v_fold_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_buckets_1228_ = lean_ctor_get(v_m_1225_, 1);
v___x_1229_ = lean_array_get_size(v_buckets_1228_);
lean_inc(v_a_1226_);
v___x_1230_ = lean_apply_1(v_inst_1224_, v_a_1226_);
v___x_1231_ = 32ULL;
v___x_1232_ = lean_unbox_uint64(v___x_1230_);
v___x_1233_ = lean_uint64_shift_right(v___x_1232_, v___x_1231_);
v___x_1234_ = lean_unbox_uint64(v___x_1230_);
lean_dec_ref(v___x_1230_);
v_fold_1235_ = lean_uint64_xor(v___x_1234_, v___x_1233_);
v___x_1236_ = 16ULL;
v___x_1237_ = lean_uint64_shift_right(v_fold_1235_, v___x_1236_);
v___x_1238_ = lean_uint64_xor(v_fold_1235_, v___x_1237_);
v___x_1239_ = lean_uint64_to_usize(v___x_1238_);
v___x_1240_ = lean_usize_of_nat(v___x_1229_);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_sub(v___x_1240_, v___x_1241_);
v___x_1243_ = lean_usize_land(v___x_1239_, v___x_1242_);
v___x_1244_ = lean_array_uget_borrowed(v_buckets_1228_, v___x_1243_);
lean_inc(v___x_1244_);
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(v_inst_1223_, v_a_1226_, v_inst_1227_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg___boxed(lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_m_1248_, lean_object* v_a_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1246_, v_inst_1247_, v_m_1248_, v_a_1249_, v_inst_1250_);
lean_dec_ref(v_inst_1250_);
lean_dec_ref(v_m_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(lean_object* v_00_u03b1_1252_, lean_object* v_00_u03b2_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_m_1256_, lean_object* v_a_1257_, lean_object* v_inst_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1254_, v_inst_1255_, v_m_1256_, v_a_1257_, v_inst_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_m_1264_, lean_object* v_a_1265_, lean_object* v_inst_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21(v_00_u03b1_1260_, v_00_u03b2_1261_, v_inst_1262_, v_inst_1263_, v_m_1264_, v_a_1265_, v_inst_1266_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_m_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_m_1270_, lean_object* v_a_1271_, lean_object* v_fallback_1272_){
_start:
{
lean_object* v_buckets_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; uint64_t v___x_1279_; uint64_t v_fold_1280_; uint64_t v___x_1281_; uint64_t v___x_1282_; uint64_t v___x_1283_; size_t v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_buckets_1273_ = lean_ctor_get(v_m_1270_, 1);
v___x_1274_ = lean_array_get_size(v_buckets_1273_);
lean_inc(v_a_1271_);
v___x_1275_ = lean_apply_1(v_inst_1269_, v_a_1271_);
v___x_1276_ = 32ULL;
v___x_1277_ = lean_unbox_uint64(v___x_1275_);
v___x_1278_ = lean_uint64_shift_right(v___x_1277_, v___x_1276_);
v___x_1279_ = lean_unbox_uint64(v___x_1275_);
lean_dec_ref(v___x_1275_);
v_fold_1280_ = lean_uint64_xor(v___x_1279_, v___x_1278_);
v___x_1281_ = 16ULL;
v___x_1282_ = lean_uint64_shift_right(v_fold_1280_, v___x_1281_);
v___x_1283_ = lean_uint64_xor(v_fold_1280_, v___x_1282_);
v___x_1284_ = lean_uint64_to_usize(v___x_1283_);
v___x_1285_ = lean_usize_of_nat(v___x_1274_);
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = lean_usize_sub(v___x_1285_, v___x_1286_);
v___x_1288_ = lean_usize_land(v___x_1284_, v___x_1287_);
v___x_1289_ = lean_array_uget_borrowed(v_buckets_1273_, v___x_1288_);
lean_inc(v___x_1289_);
v___x_1290_ = l_Std_DHashMap_Internal_AssocList_getCastD___redArg(v_inst_1268_, v_a_1271_, v_fallback_1272_, v___x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg___boxed(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_m_1293_, lean_object* v_a_1294_, lean_object* v_fallback_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1291_, v_inst_1292_, v_m_1293_, v_a_1294_, v_fallback_1295_);
lean_dec(v_fallback_1295_);
lean_dec_ref(v_m_1293_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD(lean_object* v_00_u03b1_1297_, lean_object* v_00_u03b2_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_m_1302_, lean_object* v_a_1303_, lean_object* v_fallback_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1299_, v_inst_1301_, v_m_1302_, v_a_1303_, v_fallback_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_m_1311_, lean_object* v_a_1312_, lean_object* v_fallback_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_DHashMap_Internal_Raw_u2080_getD(v_00_u03b1_1306_, v_00_u03b2_1307_, v_inst_1308_, v_inst_1309_, v_inst_1310_, v_m_1311_, v_a_1312_, v_fallback_1313_);
lean_dec(v_fallback_1313_);
lean_dec_ref(v_m_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_m_1317_, lean_object* v_a_1318_, lean_object* v_inst_1319_){
_start:
{
lean_object* v_buckets_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint64_t v___x_1323_; uint64_t v___x_1324_; uint64_t v___x_1325_; uint64_t v___x_1326_; uint64_t v_fold_1327_; uint64_t v___x_1328_; uint64_t v___x_1329_; uint64_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_buckets_1320_ = lean_ctor_get(v_m_1317_, 1);
v___x_1321_ = lean_array_get_size(v_buckets_1320_);
lean_inc(v_a_1318_);
v___x_1322_ = lean_apply_1(v_inst_1316_, v_a_1318_);
v___x_1323_ = 32ULL;
v___x_1324_ = lean_unbox_uint64(v___x_1322_);
v___x_1325_ = lean_uint64_shift_right(v___x_1324_, v___x_1323_);
v___x_1326_ = lean_unbox_uint64(v___x_1322_);
lean_dec_ref(v___x_1322_);
v_fold_1327_ = lean_uint64_xor(v___x_1326_, v___x_1325_);
v___x_1328_ = 16ULL;
v___x_1329_ = lean_uint64_shift_right(v_fold_1327_, v___x_1328_);
v___x_1330_ = lean_uint64_xor(v_fold_1327_, v___x_1329_);
v___x_1331_ = lean_uint64_to_usize(v___x_1330_);
v___x_1332_ = lean_usize_of_nat(v___x_1321_);
v___x_1333_ = ((size_t)1ULL);
v___x_1334_ = lean_usize_sub(v___x_1332_, v___x_1333_);
v___x_1335_ = lean_usize_land(v___x_1331_, v___x_1334_);
v___x_1336_ = lean_array_uget_borrowed(v_buckets_1320_, v___x_1335_);
lean_inc(v___x_1336_);
v___x_1337_ = l_Std_DHashMap_Internal_AssocList_getCast_x21___redArg(v_inst_1315_, v_a_1318_, v_inst_1319_, v___x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg___boxed(lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_m_1340_, lean_object* v_a_1341_, lean_object* v_inst_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1338_, v_inst_1339_, v_m_1340_, v_a_1341_, v_inst_1342_);
lean_dec(v_inst_1342_);
lean_dec_ref(v_m_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21(lean_object* v_00_u03b1_1344_, lean_object* v_00_u03b2_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_m_1349_, lean_object* v_a_1350_, lean_object* v_inst_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1346_, v_inst_1348_, v_m_1349_, v_a_1350_, v_inst_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_m_1358_, lean_object* v_a_1359_, lean_object* v_inst_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21(v_00_u03b1_1353_, v_00_u03b2_1354_, v_inst_1355_, v_inst_1356_, v_inst_1357_, v_m_1358_, v_a_1359_, v_inst_1360_);
lean_dec(v_inst_1360_);
lean_dec_ref(v_m_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_m_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_size_1366_; lean_object* v_buckets_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; uint64_t v___x_1370_; uint64_t v___x_1371_; uint64_t v___x_1372_; uint64_t v___x_1373_; uint64_t v_fold_1374_; uint64_t v___x_1375_; uint64_t v___x_1376_; uint64_t v___x_1377_; size_t v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; size_t v___x_1382_; lean_object* v_bkt_1383_; uint8_t v___x_1384_; 
v_size_1366_ = lean_ctor_get(v_m_1364_, 0);
v_buckets_1367_ = lean_ctor_get(v_m_1364_, 1);
v___x_1368_ = lean_array_get_size(v_buckets_1367_);
lean_inc_n(v_a_1365_, 2);
v___x_1369_ = lean_apply_1(v_inst_1363_, v_a_1365_);
v___x_1370_ = 32ULL;
v___x_1371_ = lean_unbox_uint64(v___x_1369_);
v___x_1372_ = lean_uint64_shift_right(v___x_1371_, v___x_1370_);
v___x_1373_ = lean_unbox_uint64(v___x_1369_);
lean_dec_ref(v___x_1369_);
v_fold_1374_ = lean_uint64_xor(v___x_1373_, v___x_1372_);
v___x_1375_ = 16ULL;
v___x_1376_ = lean_uint64_shift_right(v_fold_1374_, v___x_1375_);
v___x_1377_ = lean_uint64_xor(v_fold_1374_, v___x_1376_);
v___x_1378_ = lean_uint64_to_usize(v___x_1377_);
v___x_1379_ = lean_usize_of_nat(v___x_1368_);
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_sub(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_usize_land(v___x_1378_, v___x_1381_);
v_bkt_1383_ = lean_array_uget_borrowed(v_buckets_1367_, v___x_1382_);
lean_inc(v_bkt_1383_);
lean_inc_ref(v_inst_1362_);
v___x_1384_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_1362_, v_a_1365_, v_bkt_1383_);
if (v___x_1384_ == 0)
{
lean_dec(v_a_1365_);
lean_dec_ref(v_inst_1362_);
return v_m_1364_;
}
else
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
lean_inc(v_bkt_1383_);
lean_inc_ref(v_buckets_1367_);
lean_inc(v_size_1366_);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_m_1364_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; lean_object* v_unused_1399_; 
v_unused_1398_ = lean_ctor_get(v_m_1364_, 1);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_m_1364_, 0);
lean_dec(v_unused_1399_);
v___x_1386_ = v_m_1364_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_m_1364_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v_buckets_x27_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1388_ = lean_box(0);
v_buckets_x27_1389_ = lean_array_uset(v_buckets_1367_, v___x_1382_, v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(1u);
v___x_1391_ = lean_nat_sub(v_size_1366_, v___x_1390_);
lean_dec(v_size_1366_);
v___x_1392_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_1362_, v_a_1365_, v_bkt_1383_);
v___x_1393_ = lean_array_uset(v_buckets_x27_1389_, v___x_1382_, v___x_1392_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1393_);
lean_ctor_set(v___x_1386_, 0, v___x_1391_);
v___x_1395_ = v___x_1386_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase(lean_object* v_00_u03b1_1400_, lean_object* v_00_u03b2_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_m_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1402_, v_inst_1403_, v_m_1404_, v_a_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0(lean_object* v_f_1407_, lean_object* v_x_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go(lean_box(0), lean_box(0), lean_box(0), v_f_1407_, v___x_1409_, v_x_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object* v_f_1411_, lean_object* v_m_1412_){
_start:
{
lean_object* v_buckets_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1434_; 
v_buckets_1413_ = lean_ctor_get(v_m_1412_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_m_1412_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v_m_1412_, 0);
lean_dec(v_unused_1435_);
v___x_1415_ = v_m_1412_;
v_isShared_1416_ = v_isSharedCheck_1434_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_buckets_1413_);
lean_dec(v_m_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1434_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___f_1417_; lean_object* v___x_1418_; size_t v_sz_1419_; size_t v___x_1420_; lean_object* v_newBuckets_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___f_1417_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1417_, 0, v_f_1411_);
v___x_1418_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_sz_1419_ = lean_array_size(v_buckets_1413_);
v___x_1420_ = ((size_t)0ULL);
v_newBuckets_1421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1418_, v___f_1417_, v_sz_1419_, v___x_1420_, v_buckets_1413_);
v___x_1422_ = lean_unsigned_to_nat(0u);
v___x_1423_ = lean_array_get_size(v_newBuckets_1421_);
v___x_1424_ = lean_nat_dec_lt(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v_newBuckets_1421_);
lean_ctor_set(v___x_1415_, 0, v___x_1422_);
v___x_1426_ = v___x_1415_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_newBuckets_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___f_1428_; size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___f_1428_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_1429_ = lean_usize_of_nat(v___x_1423_);
lean_inc(v_newBuckets_1421_);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1418_, v___f_1428_, v_newBuckets_1421_, v___x_1420_, v___x_1429_, v___x_1422_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v_newBuckets_1421_);
lean_ctor_set(v___x_1415_, 0, v___x_1430_);
v___x_1432_ = v___x_1415_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_newBuckets_1421_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap(lean_object* v_00_u03b1_1436_, lean_object* v_00_u03b2_1437_, lean_object* v_00_u03b3_1438_, lean_object* v_f_1439_, lean_object* v_m_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1439_, v_m_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0(lean_object* v_f_1442_, lean_object* v_x_1443_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go(lean_box(0), lean_box(0), lean_box(0), v_f_1442_, v___x_1444_, v_x_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object* v_f_1446_, lean_object* v_m_1447_){
_start:
{
lean_object* v_size_1448_; lean_object* v_buckets_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1461_; 
v_size_1448_ = lean_ctor_get(v_m_1447_, 0);
v_buckets_1449_ = lean_ctor_get(v_m_1447_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_m_1447_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1451_ = v_m_1447_;
v_isShared_1452_ = v_isSharedCheck_1461_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_buckets_1449_);
lean_inc(v_size_1448_);
lean_dec(v_m_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1461_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___f_1453_; lean_object* v___x_1454_; size_t v_sz_1455_; size_t v___x_1456_; lean_object* v_newBuckets_1457_; lean_object* v___x_1459_; 
v___f_1453_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1453_, 0, v_f_1446_);
v___x_1454_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_sz_1455_ = lean_array_size(v_buckets_1449_);
v___x_1456_ = ((size_t)0ULL);
v_newBuckets_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1454_, v___f_1453_, v_sz_1455_, v___x_1456_, v_buckets_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_newBuckets_1457_);
v___x_1459_ = v___x_1451_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_size_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_newBuckets_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map(lean_object* v_00_u03b1_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_00_u03b3_1464_, lean_object* v_f_1465_, lean_object* v_m_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1465_, v_m_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0(lean_object* v_f_1468_, lean_object* v_x_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go(lean_box(0), lean_box(0), v_f_1468_, v___x_1470_, v_x_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object* v_f_1472_, lean_object* v_m_1473_){
_start:
{
lean_object* v_buckets_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1495_; 
v_buckets_1474_ = lean_ctor_get(v_m_1473_, 1);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_m_1473_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_m_1473_, 0);
lean_dec(v_unused_1496_);
v___x_1476_ = v_m_1473_;
v_isShared_1477_ = v_isSharedCheck_1495_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_buckets_1474_);
lean_dec(v_m_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1495_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___f_1478_; lean_object* v___x_1479_; size_t v_sz_1480_; size_t v___x_1481_; lean_object* v_newBuckets_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___f_1478_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filter___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1478_, 0, v_f_1472_);
v___x_1479_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_sz_1480_ = lean_array_size(v_buckets_1474_);
v___x_1481_ = ((size_t)0ULL);
v_newBuckets_1482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1479_, v___f_1478_, v_sz_1480_, v___x_1481_, v_buckets_1474_);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_array_get_size(v_newBuckets_1482_);
v___x_1485_ = lean_nat_dec_lt(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1487_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v_newBuckets_1482_);
lean_ctor_set(v___x_1476_, 0, v___x_1483_);
v___x_1487_ = v___x_1476_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_newBuckets_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
lean_object* v___f_1489_; size_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___f_1489_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__10));
v___x_1490_ = lean_usize_of_nat(v___x_1484_);
lean_inc(v_newBuckets_1482_);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1479_, v___f_1489_, v_newBuckets_1482_, v___x_1481_, v___x_1490_, v___x_1483_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v_newBuckets_1482_);
lean_ctor_set(v___x_1476_, 0, v___x_1491_);
v___x_1493_ = v___x_1476_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_newBuckets_1482_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter(lean_object* v_00_u03b1_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_f_1499_, lean_object* v_m_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1499_, v_m_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0(lean_object* v_inst_1502_, lean_object* v_inst_1503_, lean_object* v_x_1504_, lean_object* v_____s_1505_){
_start:
{
lean_object* v_fst_1506_; lean_object* v_snd_1507_; lean_object* v_r_1508_; lean_object* v___x_1509_; 
v_fst_1506_ = lean_ctor_get(v_x_1504_, 0);
lean_inc(v_fst_1506_);
v_snd_1507_ = lean_ctor_get(v_x_1504_, 1);
lean_inc(v_snd_1507_);
lean_dec_ref(v_x_1504_);
v_r_1508_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1502_, v_inst_1503_, v_____s_1505_, v_fst_1506_, v_snd_1507_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_r_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_m_1513_, lean_object* v_l_1514_){
_start:
{
lean_object* v___f_1515_; lean_object* v___x_1516_; 
v___f_1515_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1515_, 0, v_inst_1511_);
lean_closure_set(v___f_1515_, 1, v_inst_1512_);
v___x_1516_ = lean_apply_4(v_inst_1510_, lean_box(0), v_l_1514_, v_m_1513_, v___f_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany(lean_object* v_00_u03b1_1517_, lean_object* v_00_u03b2_1518_, lean_object* v_00_u03c1_1519_, lean_object* v_inst_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_m_1523_, lean_object* v_l_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_1520_, v_inst_1521_, v_inst_1522_, v_m_1523_, v_l_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0(lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_x_1528_, lean_object* v_____s_1529_){
_start:
{
lean_object* v_fst_1530_; lean_object* v_r_1531_; lean_object* v___x_1532_; 
v_fst_1530_ = lean_ctor_get(v_x_1528_, 0);
lean_inc(v_fst_1530_);
lean_dec_ref(v_x_1528_);
v_r_1531_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1526_, v_inst_1527_, v_____s_1529_, v_fst_1530_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_r_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object* v_inst_1533_, lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_m_1536_, lean_object* v_l_1537_){
_start:
{
lean_object* v___f_1538_; lean_object* v___x_1539_; 
v___f_1538_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1538_, 0, v_inst_1534_);
lean_closure_set(v___f_1538_, 1, v_inst_1535_);
v___x_1539_ = lean_apply_4(v_inst_1533_, lean_box(0), v_l_1537_, v_m_1536_, v___f_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries(lean_object* v_00_u03b1_1540_, lean_object* v_00_u03b2_1541_, lean_object* v_00_u03c1_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_m_1546_, lean_object* v_l_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_1543_, v_inst_1544_, v_inst_1545_, v_m_1546_, v_l_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0(lean_object* v_inst_1549_, lean_object* v_inst_1550_, lean_object* v_x_1551_, lean_object* v_____s_1552_){
_start:
{
lean_object* v_fst_1553_; lean_object* v_snd_1554_; lean_object* v_r_1555_; lean_object* v___x_1556_; 
v_fst_1553_ = lean_ctor_get(v_x_1551_, 0);
lean_inc(v_fst_1553_);
v_snd_1554_ = lean_ctor_get(v_x_1551_, 1);
lean_inc(v_snd_1554_);
lean_dec_ref(v_x_1551_);
v_r_1555_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1549_, v_inst_1550_, v_____s_1552_, v_fst_1553_, v_snd_1554_);
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_r_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg(lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_inst_1559_, lean_object* v_m_1560_, lean_object* v_l_1561_){
_start:
{
lean_object* v___f_1562_; lean_object* v___x_1563_; 
v___f_1562_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1562_, 0, v_inst_1558_);
lean_closure_set(v___f_1562_, 1, v_inst_1559_);
v___x_1563_ = lean_apply_4(v_inst_1557_, lean_box(0), v_l_1561_, v_m_1560_, v___f_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_00_u03c1_1566_, lean_object* v_inst_1567_, lean_object* v_inst_1568_, lean_object* v_inst_1569_, lean_object* v_m_1570_, lean_object* v_l_1571_){
_start:
{
lean_object* v___f_1572_; lean_object* v___x_1573_; 
v___f_1572_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_insertManyIfNew___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1572_, 0, v_inst_1568_);
lean_closure_set(v___f_1572_, 1, v_inst_1569_);
v___x_1573_ = lean_apply_4(v_inst_1567_, lean_box(0), v_l_1571_, v_m_1570_, v___f_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_m_1576_, lean_object* v_sofar_1577_, lean_object* v_k_1578_){
_start:
{
lean_object* v___x_1579_; 
lean_inc_ref(v_inst_1575_);
lean_inc_ref(v_inst_1574_);
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1574_, v_inst_1575_, v_m_1576_, v_k_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref(v_inst_1575_);
lean_dec_ref(v_inst_1574_);
return v_sofar_1577_;
}
else
{
lean_object* v_val_1580_; lean_object* v_fst_1581_; lean_object* v_snd_1582_; lean_object* v___x_1583_; 
v_val_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v_fst_1581_ = lean_ctor_get(v_val_1580_, 0);
lean_inc(v_fst_1581_);
v_snd_1582_ = lean_ctor_get(v_val_1580_, 1);
lean_inc(v_snd_1582_);
lean_dec(v_val_1580_);
v___x_1583_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1574_, v_inst_1575_, v_sofar_1577_, v_fst_1581_, v_snd_1582_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg___boxed(lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_m_1586_, lean_object* v_sofar_1587_, lean_object* v_k_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___redArg(v_inst_1584_, v_inst_1585_, v_m_1586_, v_sofar_1587_, v_k_1588_);
lean_dec_ref(v_m_1586_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(lean_object* v_00_u03b1_1590_, lean_object* v_00_u03b2_1591_, lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_m_1594_, lean_object* v_sofar_1595_, lean_object* v_k_1596_){
_start:
{
lean_object* v___x_1597_; 
lean_inc_ref(v_inst_1593_);
lean_inc_ref(v_inst_1592_);
v___x_1597_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1592_, v_inst_1593_, v_m_1594_, v_k_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref(v_inst_1593_);
lean_dec_ref(v_inst_1592_);
return v_sofar_1595_;
}
else
{
lean_object* v_val_1598_; lean_object* v_fst_1599_; lean_object* v_snd_1600_; lean_object* v___x_1601_; 
v_val_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_val_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v_fst_1599_ = lean_ctor_get(v_val_1598_, 0);
lean_inc(v_fst_1599_);
v_snd_1600_ = lean_ctor_get(v_val_1598_, 1);
lean_inc(v_snd_1600_);
lean_dec(v_val_1598_);
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1592_, v_inst_1593_, v_sofar_1595_, v_fst_1599_, v_snd_1600_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn___boxed(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_m_1606_, lean_object* v_sofar_1607_, lean_object* v_k_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn(v_00_u03b1_1602_, v_00_u03b2_1603_, v_inst_1604_, v_inst_1605_, v_m_1606_, v_sofar_1607_, v_k_1608_);
lean_dec_ref(v_m_1606_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_m_u2081_1612_, lean_object* v_x1_1613_, lean_object* v_x2_1614_, lean_object* v_x3_1615_){
_start:
{
lean_object* v___x_1616_; 
lean_inc_ref(v_inst_1611_);
lean_inc_ref(v_inst_1610_);
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1610_, v_inst_1611_, v_m_u2081_1612_, v_x2_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_dec_ref(v_inst_1611_);
lean_dec_ref(v_inst_1610_);
return v_x1_1613_;
}
else
{
lean_object* v_val_1617_; lean_object* v_fst_1618_; lean_object* v_snd_1619_; lean_object* v___x_1620_; 
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v_fst_1618_ = lean_ctor_get(v_val_1617_, 0);
lean_inc(v_fst_1618_);
v_snd_1619_ = lean_ctor_get(v_val_1617_, 1);
lean_inc(v_snd_1619_);
lean_dec(v_val_1617_);
v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1610_, v_inst_1611_, v_x1_1613_, v_fst_1618_, v_snd_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed(lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_m_u2081_1623_, lean_object* v_x1_1624_, lean_object* v_x2_1625_, lean_object* v_x3_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0(v_inst_1621_, v_inst_1622_, v_m_u2081_1623_, v_x1_1624_, v_x2_1625_, v_x3_1626_);
lean_dec(v_x3_1626_);
lean_dec_ref(v_m_u2081_1623_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1(lean_object* v___x_1628_, lean_object* v___f_1629_, lean_object* v_acc_1630_, lean_object* v_l_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1628_, v___f_1629_, v_acc_1630_, v_l_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_unsigned_to_nat(16u);
v___x_1635_ = lean_mk_array(v___x_1634_, v___x_1633_);
return v___x_1635_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__0);
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_m_u2081_1641_, lean_object* v_m_u2082_1642_){
_start:
{
lean_object* v___x_1643_; lean_object* v_buckets_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1643_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_buckets_1644_ = lean_ctor_get(v_m_u2082_1642_, 1);
lean_inc_ref(v_buckets_1644_);
lean_dec_ref(v_m_u2082_1642_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1, &l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1_once, _init_l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___closed__1);
v___x_1647_ = lean_array_get_size(v_buckets_1644_);
v___x_1648_ = lean_nat_dec_lt(v___x_1645_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v_buckets_1644_);
lean_dec_ref(v_m_u2081_1641_);
lean_dec_ref(v_inst_1640_);
lean_dec_ref(v_inst_1639_);
return v___x_1646_;
}
else
{
lean_object* v___f_1649_; lean_object* v___f_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v___f_1649_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1649_, 0, v_inst_1639_);
lean_closure_set(v___f_1649_, 1, v_inst_1640_);
lean_closure_set(v___f_1649_, 2, v_m_u2081_1641_);
v___f_1650_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1650_, 0, v___x_1643_);
lean_closure_set(v___f_1650_, 1, v___f_1649_);
v___x_1651_ = ((size_t)0ULL);
v___x_1652_ = lean_usize_of_nat(v___x_1647_);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1643_, v___f_1650_, v_buckets_1644_, v___x_1651_, v___x_1652_, v___x_1646_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmaller(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_m_u2081_1658_, lean_object* v_m_u2082_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(v_inst_1656_, v_inst_1657_, v_m_u2081_1658_, v_m_u2082_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0(lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v_acc_1665_){
_start:
{
lean_object* v_r_1666_; lean_object* v___x_1667_; 
v_r_1666_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1661_, v_inst_1662_, v_acc_1665_, v_a_1663_, v_b_1664_);
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_r_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1(lean_object* v___x_1668_, lean_object* v___f_1669_, lean_object* v_a_1670_, lean_object* v_x_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1668_, v___f_1669_, v_a_1670_, v___y_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union___redArg(lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_m_u2081_1678_, lean_object* v_m_u2082_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v_size_1681_; lean_object* v_buckets_1682_; lean_object* v_size_1683_; uint8_t v___x_1684_; 
v___x_1680_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_size_1681_ = lean_ctor_get(v_m_u2081_1678_, 0);
v_buckets_1682_ = lean_ctor_get(v_m_u2081_1678_, 1);
v_size_1683_ = lean_ctor_get(v_m_u2082_1679_, 0);
v___x_1684_ = lean_nat_dec_le(v_size_1681_, v_size_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___f_1685_; lean_object* v___x_1686_; 
v___f_1685_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1685_, v_inst_1676_, v_inst_1677_, v_m_u2081_1678_, v_m_u2082_1679_);
return v___x_1686_;
}
else
{
lean_object* v___f_1687_; lean_object* v___f_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
lean_inc_ref(v_buckets_1682_);
lean_dec_ref(v_m_u2081_1678_);
v___f_1687_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1687_, 0, v_inst_1676_);
lean_closure_set(v___f_1687_, 1, v_inst_1677_);
v___f_1688_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1688_, 0, v___x_1680_);
lean_closure_set(v___f_1688_, 1, v___f_1687_);
v_sz_1689_ = lean_array_size(v_buckets_1682_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1680_, v_buckets_1682_, v___f_1688_, v_sz_1689_, v___x_1690_, v_m_u2082_1679_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union(lean_object* v_00_u03b1_1692_, lean_object* v_00_u03b2_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_m_u2081_1696_, lean_object* v_m_u2082_1697_){
_start:
{
lean_object* v___x_1698_; lean_object* v_size_1699_; lean_object* v_buckets_1700_; lean_object* v_size_1701_; uint8_t v___x_1702_; 
v___x_1698_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v_size_1699_ = lean_ctor_get(v_m_u2081_1696_, 0);
v_buckets_1700_ = lean_ctor_get(v_m_u2081_1696_, 1);
v_size_1701_ = lean_ctor_get(v_m_u2082_1697_, 0);
v___x_1702_ = lean_nat_dec_le(v_size_1699_, v_size_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___f_1703_; lean_object* v___x_1704_; 
v___f_1703_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1703_, v_inst_1694_, v_inst_1695_, v_m_u2081_1696_, v_m_u2082_1697_);
return v___x_1704_;
}
else
{
lean_object* v___f_1705_; lean_object* v___f_1706_; size_t v_sz_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
lean_inc_ref(v_buckets_1700_);
lean_dec_ref(v_m_u2081_1696_);
v___f_1705_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1705_, 0, v_inst_1694_);
lean_closure_set(v___f_1705_, 1, v_inst_1695_);
v___f_1706_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1706_, 0, v___x_1698_);
lean_closure_set(v___f_1706_, 1, v___f_1705_);
v_sz_1707_ = lean_array_size(v_buckets_1700_);
v___x_1708_ = ((size_t)0ULL);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1698_, v_buckets_1700_, v___f_1706_, v_sz_1707_, v___x_1708_, v_m_u2082_1697_);
return v___x_1709_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_m_u2082_1712_, lean_object* v_k_1713_, lean_object* v_x_1714_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1710_, v_inst_1711_, v_m_u2082_1712_, v_k_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed(lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_m_u2082_1718_, lean_object* v_k_1719_, lean_object* v_x_1720_){
_start:
{
uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_res_1721_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0(v_inst_1716_, v_inst_1717_, v_m_u2082_1718_, v_k_1719_, v_x_1720_);
lean_dec(v_x_1720_);
lean_dec_ref(v_m_u2082_1718_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_m_u2081_1725_, lean_object* v_m_u2082_1726_){
_start:
{
lean_object* v_size_1727_; lean_object* v_size_1728_; uint8_t v___x_1729_; 
v_size_1727_ = lean_ctor_get(v_m_u2081_1725_, 0);
v_size_1728_ = lean_ctor_get(v_m_u2082_1726_, 0);
v___x_1729_ = lean_nat_dec_le(v_size_1727_, v_size_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Std_DHashMap_Internal_Raw_u2080_interSmaller___redArg(v_inst_1723_, v_inst_1724_, v_m_u2081_1725_, v_m_u2082_1726_);
return v___x_1730_;
}
else
{
lean_object* v___f_1731_; lean_object* v___x_1732_; 
v___f_1731_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_inter___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1731_, 0, v_inst_1723_);
lean_closure_set(v___f_1731_, 1, v_inst_1724_);
lean_closure_set(v___f_1731_, 2, v_m_u2082_1726_);
v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1731_, v_m_u2081_1725_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter(lean_object* v_00_u03b1_1733_, lean_object* v_00_u03b2_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_m_u2081_1737_, lean_object* v_m_u2082_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1735_, v_inst_1736_, v_m_u2081_1737_, v_m_u2082_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_m_u2082_1743_, uint8_t v___x_1744_, lean_object* v___x_1745_, lean_object* v___x_1746_, lean_object* v_a_1747_, lean_object* v_b_1748_, lean_object* v_acc_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
lean_inc(v_a_1747_);
v___x_1750_ = lean_apply_1(v_inst_1740_, v_a_1747_);
v___x_1751_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1741_, v_inst_1742_, v_m_u2082_1743_, v_a_1747_);
v___x_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1752_, 0, v_b_1748_);
v___x_1753_ = l_Option_instBEq_beq___redArg(v___x_1750_, v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec_ref(v___x_1746_);
v___x_1754_ = lean_box(v___x_1744_);
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v___x_1745_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1746_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed(lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_m_u2082_1762_, lean_object* v___x_1763_, lean_object* v___x_1764_, lean_object* v___x_1765_, lean_object* v_a_1766_, lean_object* v_b_1767_, lean_object* v_acc_1768_){
_start:
{
uint8_t v___x_236__boxed_1769_; lean_object* v_res_1770_; 
v___x_236__boxed_1769_ = lean_unbox(v___x_1763_);
v_res_1770_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0(v_inst_1759_, v_inst_1760_, v_inst_1761_, v_m_u2082_1762_, v___x_236__boxed_1769_, v___x_1764_, v___x_1765_, v_a_1766_, v_b_1767_, v_acc_1768_);
lean_dec_ref(v_acc_1768_);
lean_dec_ref(v_m_u2082_1762_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1(lean_object* v___x_1771_, lean_object* v___f_1772_, lean_object* v_a_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1771_, v___f_1772_, v_a_1773_, v___y_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_m_u2081_1783_, lean_object* v_m_u2082_1784_){
_start:
{
lean_object* v_size_1785_; lean_object* v_buckets_1786_; lean_object* v_size_1787_; uint8_t v___x_1788_; 
v_size_1785_ = lean_ctor_get(v_m_u2081_1783_, 0);
lean_inc(v_size_1785_);
v_buckets_1786_ = lean_ctor_get(v_m_u2081_1783_, 1);
lean_inc_ref(v_buckets_1786_);
lean_dec_ref(v_m_u2081_1783_);
v_size_1787_ = lean_ctor_get(v_m_u2082_1784_, 0);
v___x_1788_ = lean_nat_dec_eq(v_size_1785_, v_size_1787_);
lean_dec(v_size_1785_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v_buckets_1786_);
lean_dec_ref(v_m_u2082_1784_);
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
return v___x_1788_;
}
else
{
uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___f_1794_; lean_object* v___f_1795_; size_t v_sz_1796_; size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v_fst_1799_; 
v___x_1789_ = 0;
v___x_1790_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_1791_ = lean_box(0);
v___x_1792_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0));
v___x_1793_ = lean_box(v___x_1789_);
v___f_1794_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1794_, 0, v_inst_1782_);
lean_closure_set(v___f_1794_, 1, v_inst_1780_);
lean_closure_set(v___f_1794_, 2, v_inst_1781_);
lean_closure_set(v___f_1794_, 3, v_m_u2082_1784_);
lean_closure_set(v___f_1794_, 4, v___x_1793_);
lean_closure_set(v___f_1794_, 5, v___x_1791_);
lean_closure_set(v___f_1794_, 6, v___x_1792_);
v___f_1795_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1795_, 0, v___x_1790_);
lean_closure_set(v___f_1795_, 1, v___f_1794_);
v_sz_1796_ = lean_array_size(v_buckets_1786_);
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1790_, v_buckets_1786_, v___f_1795_, v_sz_1796_, v___x_1797_, v___x_1792_);
v_fst_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_fst_1799_);
lean_dec(v___x_1798_);
if (lean_obj_tag(v_fst_1799_) == 0)
{
return v___x_1788_;
}
else
{
lean_object* v_val_1800_; uint8_t v___x_1801_; 
v_val_1800_ = lean_ctor_get(v_fst_1799_, 0);
lean_inc(v_val_1800_);
lean_dec_ref_known(v_fst_1799_, 1);
v___x_1801_ = lean_unbox(v_val_1800_);
lean_dec(v_val_1800_);
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___boxed(lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_m_u2081_1805_, lean_object* v_m_u2082_1806_){
_start:
{
uint8_t v_res_1807_; lean_object* v_r_1808_; 
v_res_1807_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1802_, v_inst_1803_, v_inst_1804_, v_m_u2081_1805_, v_m_u2082_1806_);
v_r_1808_ = lean_box(v_res_1807_);
return v_r_1808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_m_u2081_1815_, lean_object* v_m_u2082_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_1811_, v_inst_1813_, v_inst_1814_, v_m_u2081_1815_, v_m_u2082_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_beq___boxed(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_m_u2081_1824_, lean_object* v_m_u2082_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Std_DHashMap_Internal_Raw_u2080_beq(v_00_u03b1_1818_, v_00_u03b2_1819_, v_inst_1820_, v_inst_1821_, v_inst_1822_, v_inst_1823_, v_m_u2081_1824_, v_m_u2082_1825_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_m_u2082_1830_, uint8_t v___x_1831_, lean_object* v_k_1832_, lean_object* v_x_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1828_, v_inst_1829_, v_m_u2082_1830_, v_k_1832_);
if (v___x_1834_ == 0)
{
return v___x_1831_;
}
else
{
uint8_t v___x_1835_; 
v___x_1835_ = 0;
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed(lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_m_u2082_1838_, lean_object* v___x_1839_, lean_object* v_k_1840_, lean_object* v_x_1841_){
_start:
{
uint8_t v___x_68__boxed_1842_; uint8_t v_res_1843_; lean_object* v_r_1844_; 
v___x_68__boxed_1842_ = lean_unbox(v___x_1839_);
v_res_1843_ = l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0(v_inst_1836_, v_inst_1837_, v_m_u2082_1838_, v___x_68__boxed_1842_, v_k_1840_, v_x_1841_);
lean_dec(v_x_1841_);
lean_dec_ref(v_m_u2082_1838_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff___redArg(lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_m_u2081_1847_, lean_object* v_m_u2082_1848_){
_start:
{
lean_object* v_size_1849_; lean_object* v_size_1850_; uint8_t v___x_1851_; 
v_size_1849_ = lean_ctor_get(v_m_u2081_1847_, 0);
v_size_1850_ = lean_ctor_get(v_m_u2082_1848_, 0);
v___x_1851_ = lean_nat_dec_le(v_size_1849_, v_size_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___f_1852_; lean_object* v___x_1853_; 
v___f_1852_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1852_, v_inst_1845_, v_inst_1846_, v_m_u2081_1847_, v_m_u2082_1848_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_box(v___x_1851_);
v___f_1855_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1855_, 0, v_inst_1845_);
lean_closure_set(v___f_1855_, 1, v_inst_1846_);
lean_closure_set(v___f_1855_, 2, v_m_u2082_1848_);
lean_closure_set(v___f_1855_, 3, v___x_1854_);
v___x_1856_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1855_, v_m_u2081_1847_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff(lean_object* v_00_u03b1_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_m_u2081_1861_, lean_object* v_m_u2082_1862_){
_start:
{
lean_object* v_size_1863_; lean_object* v_size_1864_; uint8_t v___x_1865_; 
v_size_1863_ = lean_ctor_get(v_m_u2081_1861_, 0);
v_size_1864_ = lean_ctor_get(v_m_u2082_1862_, 0);
v___x_1865_ = lean_nat_dec_le(v_size_1863_, v_size_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___f_1866_; lean_object* v___x_1867_; 
v___f_1866_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_union___redArg___closed__0));
v___x_1867_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1866_, v_inst_1859_, v_inst_1860_, v_m_u2081_1861_, v_m_u2082_1862_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v___f_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_box(v___x_1865_);
v___f_1869_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1869_, 0, v_inst_1859_);
lean_closure_set(v___f_1869_, 1, v_inst_1860_);
lean_closure_set(v___f_1869_, 2, v_m_u2082_1862_);
lean_closure_set(v___f_1869_, 3, v___x_1868_);
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1869_, v_m_u2081_1861_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_m_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_buckets_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint64_t v___x_1878_; uint64_t v___x_1879_; uint64_t v___x_1880_; uint64_t v___x_1881_; uint64_t v_fold_1882_; uint64_t v___x_1883_; uint64_t v___x_1884_; uint64_t v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_buckets_1875_ = lean_ctor_get(v_m_1873_, 1);
v___x_1876_ = lean_array_get_size(v_buckets_1875_);
lean_inc(v_a_1874_);
v___x_1877_ = lean_apply_1(v_inst_1872_, v_a_1874_);
v___x_1878_ = 32ULL;
v___x_1879_ = lean_unbox_uint64(v___x_1877_);
v___x_1880_ = lean_uint64_shift_right(v___x_1879_, v___x_1878_);
v___x_1881_ = lean_unbox_uint64(v___x_1877_);
lean_dec_ref(v___x_1877_);
v_fold_1882_ = lean_uint64_xor(v___x_1881_, v___x_1880_);
v___x_1883_ = 16ULL;
v___x_1884_ = lean_uint64_shift_right(v_fold_1882_, v___x_1883_);
v___x_1885_ = lean_uint64_xor(v_fold_1882_, v___x_1884_);
v___x_1886_ = lean_uint64_to_usize(v___x_1885_);
v___x_1887_ = lean_usize_of_nat(v___x_1876_);
v___x_1888_ = ((size_t)1ULL);
v___x_1889_ = lean_usize_sub(v___x_1887_, v___x_1888_);
v___x_1890_ = lean_usize_land(v___x_1886_, v___x_1889_);
v___x_1891_ = lean_array_uget_borrowed(v_buckets_1875_, v___x_1890_);
lean_inc(v___x_1891_);
v___x_1892_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1871_, v_a_1874_, v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg___boxed(lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_m_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1893_, v_inst_1894_, v_m_1895_, v_a_1896_);
lean_dec_ref(v_m_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(lean_object* v_00_u03b1_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_m_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1900_, v_inst_1901_, v_m_1902_, v_a_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_m_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f(v_00_u03b1_1905_, v_00_u03b2_1906_, v_inst_1907_, v_inst_1908_, v_m_1909_, v_a_1910_);
lean_dec_ref(v_m_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_m_u2082_1914_, lean_object* v_inst_1915_, uint8_t v___x_1916_, lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v_a_1919_, lean_object* v_b_1920_, lean_object* v_acc_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1912_, v_inst_1913_, v_m_u2082_1914_, v_a_1919_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_b_1920_);
v___x_1924_ = l_Option_instBEq_beq___redArg(v_inst_1915_, v___x_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec_ref(v___x_1918_);
v___x_1925_ = lean_box(v___x_1916_);
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1917_);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1918_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed(lean_object* v_inst_1930_, lean_object* v_inst_1931_, lean_object* v_m_u2082_1932_, lean_object* v_inst_1933_, lean_object* v___x_1934_, lean_object* v___x_1935_, lean_object* v___x_1936_, lean_object* v_a_1937_, lean_object* v_b_1938_, lean_object* v_acc_1939_){
_start:
{
uint8_t v___x_229__boxed_1940_; lean_object* v_res_1941_; 
v___x_229__boxed_1940_ = lean_unbox(v___x_1934_);
v_res_1941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0(v_inst_1930_, v_inst_1931_, v_m_u2082_1932_, v_inst_1933_, v___x_229__boxed_1940_, v___x_1935_, v___x_1936_, v_a_1937_, v_b_1938_, v_acc_1939_);
lean_dec_ref(v_acc_1939_);
lean_dec_ref(v_m_u2082_1932_);
return v_res_1941_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_m_u2081_1945_, lean_object* v_m_u2082_1946_){
_start:
{
lean_object* v_size_1947_; lean_object* v_buckets_1948_; lean_object* v_size_1949_; uint8_t v___x_1950_; 
v_size_1947_ = lean_ctor_get(v_m_u2081_1945_, 0);
lean_inc(v_size_1947_);
v_buckets_1948_ = lean_ctor_get(v_m_u2081_1945_, 1);
lean_inc_ref(v_buckets_1948_);
lean_dec_ref(v_m_u2081_1945_);
v_size_1949_ = lean_ctor_get(v_m_u2082_1946_, 0);
v___x_1950_ = lean_nat_dec_eq(v_size_1947_, v_size_1949_);
lean_dec(v_size_1947_);
if (v___x_1950_ == 0)
{
lean_dec_ref(v_buckets_1948_);
lean_dec_ref(v_m_u2082_1946_);
lean_dec_ref(v_inst_1944_);
lean_dec_ref(v_inst_1943_);
lean_dec_ref(v_inst_1942_);
return v___x_1950_;
}
else
{
uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; size_t v_sz_1958_; size_t v___x_1959_; lean_object* v___x_1960_; lean_object* v_fst_1961_; 
v___x_1951_ = 0;
v___x_1952_ = ((lean_object*)(l_Std_DHashMap_Internal_computeSize___redArg___closed__9));
v___x_1953_ = lean_box(0);
v___x_1954_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___closed__0));
v___x_1955_ = lean_box(v___x_1951_);
v___f_1956_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___lam__0___boxed), 10, 7);
lean_closure_set(v___f_1956_, 0, v_inst_1942_);
lean_closure_set(v___f_1956_, 1, v_inst_1943_);
lean_closure_set(v___f_1956_, 2, v_m_u2082_1946_);
lean_closure_set(v___f_1956_, 3, v_inst_1944_);
lean_closure_set(v___f_1956_, 4, v___x_1955_);
lean_closure_set(v___f_1956_, 5, v___x_1953_);
lean_closure_set(v___f_1956_, 6, v___x_1954_);
v___f_1957_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_beq___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1957_, 0, v___x_1952_);
lean_closure_set(v___f_1957_, 1, v___f_1956_);
v_sz_1958_ = lean_array_size(v_buckets_1948_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1952_, v_buckets_1948_, v___f_1957_, v_sz_1958_, v___x_1959_, v___x_1954_);
v_fst_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_fst_1961_);
lean_dec(v___x_1960_);
if (lean_obj_tag(v_fst_1961_) == 0)
{
return v___x_1950_;
}
else
{
lean_object* v_val_1962_; uint8_t v___x_1963_; 
v_val_1962_ = lean_ctor_get(v_fst_1961_, 0);
lean_inc(v_val_1962_);
lean_dec_ref_known(v_fst_1961_, 1);
v___x_1963_ = lean_unbox(v_val_1962_);
lean_dec(v_val_1962_);
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg___boxed(lean_object* v_inst_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_m_u2081_1967_, lean_object* v_m_u2082_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1964_, v_inst_1965_, v_inst_1966_, v_m_u2081_1967_, v_m_u2082_1968_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq(lean_object* v_00_u03b1_1971_, lean_object* v_00_u03b2_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_m_u2081_1976_, lean_object* v_m_u2082_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1973_, v_inst_1974_, v_inst_1975_, v_m_u2081_1976_, v_m_u2082_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_beq___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_00_u03b2_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_m_u2081_1984_, lean_object* v_m_u2082_1985_){
_start:
{
uint8_t v_res_1986_; lean_object* v_r_1987_; 
v_res_1986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq(v_00_u03b1_1979_, v_00_u03b2_1980_, v_inst_1981_, v_inst_1982_, v_inst_1983_, v_m_u2081_1984_, v_m_u2082_1985_);
v_r_1987_ = lean_box(v_res_1986_);
return v_r_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_m_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_buckets_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint64_t v___x_1995_; uint64_t v___x_1996_; uint64_t v___x_1997_; uint64_t v___x_1998_; uint64_t v_fold_1999_; uint64_t v___x_2000_; uint64_t v___x_2001_; uint64_t v___x_2002_; size_t v___x_2003_; size_t v___x_2004_; size_t v___x_2005_; size_t v___x_2006_; size_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_buckets_1992_ = lean_ctor_get(v_m_1990_, 1);
v___x_1993_ = lean_array_get_size(v_buckets_1992_);
lean_inc(v_a_1991_);
v___x_1994_ = lean_apply_1(v_inst_1989_, v_a_1991_);
v___x_1995_ = 32ULL;
v___x_1996_ = lean_unbox_uint64(v___x_1994_);
v___x_1997_ = lean_uint64_shift_right(v___x_1996_, v___x_1995_);
v___x_1998_ = lean_unbox_uint64(v___x_1994_);
lean_dec_ref(v___x_1994_);
v_fold_1999_ = lean_uint64_xor(v___x_1998_, v___x_1997_);
v___x_2000_ = 16ULL;
v___x_2001_ = lean_uint64_shift_right(v_fold_1999_, v___x_2000_);
v___x_2002_ = lean_uint64_xor(v_fold_1999_, v___x_2001_);
v___x_2003_ = lean_uint64_to_usize(v___x_2002_);
v___x_2004_ = lean_usize_of_nat(v___x_1993_);
v___x_2005_ = ((size_t)1ULL);
v___x_2006_ = lean_usize_sub(v___x_2004_, v___x_2005_);
v___x_2007_ = lean_usize_land(v___x_2003_, v___x_2006_);
v___x_2008_ = lean_array_uget_borrowed(v_buckets_1992_, v___x_2007_);
lean_inc(v___x_2008_);
v___x_2009_ = l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1988_, v_a_1991_, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg___boxed(lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_m_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_2010_, v_inst_2011_, v_m_2012_, v_a_2013_);
lean_dec_ref(v_m_2012_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get(lean_object* v_00_u03b1_2015_, lean_object* v_00_u03b2_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_m_2019_, lean_object* v_a_2020_, lean_object* v_hma_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_2017_, v_inst_2018_, v_m_2019_, v_a_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_00_u03b2_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_m_2027_, lean_object* v_a_2028_, lean_object* v_hma_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get(v_00_u03b1_2023_, v_00_u03b2_2024_, v_inst_2025_, v_inst_2026_, v_m_2027_, v_a_2028_, v_hma_2029_);
lean_dec_ref(v_m_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_m_2033_, lean_object* v_a_2034_, lean_object* v_fallback_2035_){
_start:
{
lean_object* v_buckets_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint64_t v___x_2039_; uint64_t v___x_2040_; uint64_t v___x_2041_; uint64_t v___x_2042_; uint64_t v_fold_2043_; uint64_t v___x_2044_; uint64_t v___x_2045_; uint64_t v___x_2046_; size_t v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_buckets_2036_ = lean_ctor_get(v_m_2033_, 1);
v___x_2037_ = lean_array_get_size(v_buckets_2036_);
lean_inc(v_a_2034_);
v___x_2038_ = lean_apply_1(v_inst_2032_, v_a_2034_);
v___x_2039_ = 32ULL;
v___x_2040_ = lean_unbox_uint64(v___x_2038_);
v___x_2041_ = lean_uint64_shift_right(v___x_2040_, v___x_2039_);
v___x_2042_ = lean_unbox_uint64(v___x_2038_);
lean_dec_ref(v___x_2038_);
v_fold_2043_ = lean_uint64_xor(v___x_2042_, v___x_2041_);
v___x_2044_ = 16ULL;
v___x_2045_ = lean_uint64_shift_right(v_fold_2043_, v___x_2044_);
v___x_2046_ = lean_uint64_xor(v_fold_2043_, v___x_2045_);
v___x_2047_ = lean_uint64_to_usize(v___x_2046_);
v___x_2048_ = lean_usize_of_nat(v___x_2037_);
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_sub(v___x_2048_, v___x_2049_);
v___x_2051_ = lean_usize_land(v___x_2047_, v___x_2050_);
v___x_2052_ = lean_array_uget_borrowed(v_buckets_2036_, v___x_2051_);
lean_inc(v___x_2052_);
v___x_2053_ = l_Std_DHashMap_Internal_AssocList_getD___redArg(v_inst_2031_, v_a_2034_, v_fallback_2035_, v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg___boxed(lean_object* v_inst_2054_, lean_object* v_inst_2055_, lean_object* v_m_2056_, lean_object* v_a_2057_, lean_object* v_fallback_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_2054_, v_inst_2055_, v_m_2056_, v_a_2057_, v_fallback_2058_);
lean_dec(v_fallback_2058_);
lean_dec_ref(v_m_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_m_2064_, lean_object* v_a_2065_, lean_object* v_fallback_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_2062_, v_inst_2063_, v_m_2064_, v_a_2065_, v_fallback_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___boxed(lean_object* v_00_u03b1_2068_, lean_object* v_00_u03b2_2069_, lean_object* v_inst_2070_, lean_object* v_inst_2071_, lean_object* v_m_2072_, lean_object* v_a_2073_, lean_object* v_fallback_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD(v_00_u03b1_2068_, v_00_u03b2_2069_, v_inst_2070_, v_inst_2071_, v_m_2072_, v_a_2073_, v_fallback_2074_);
lean_dec(v_fallback_2074_);
lean_dec_ref(v_m_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_m_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_buckets_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint64_t v___x_2084_; uint64_t v___x_2085_; uint64_t v___x_2086_; uint64_t v___x_2087_; uint64_t v_fold_2088_; uint64_t v___x_2089_; uint64_t v___x_2090_; uint64_t v___x_2091_; size_t v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_buckets_2081_ = lean_ctor_get(v_m_2079_, 1);
v___x_2082_ = lean_array_get_size(v_buckets_2081_);
lean_inc(v_a_2080_);
v___x_2083_ = lean_apply_1(v_inst_2077_, v_a_2080_);
v___x_2084_ = 32ULL;
v___x_2085_ = lean_unbox_uint64(v___x_2083_);
v___x_2086_ = lean_uint64_shift_right(v___x_2085_, v___x_2084_);
v___x_2087_ = lean_unbox_uint64(v___x_2083_);
lean_dec_ref(v___x_2083_);
v_fold_2088_ = lean_uint64_xor(v___x_2087_, v___x_2086_);
v___x_2089_ = 16ULL;
v___x_2090_ = lean_uint64_shift_right(v_fold_2088_, v___x_2089_);
v___x_2091_ = lean_uint64_xor(v_fold_2088_, v___x_2090_);
v___x_2092_ = lean_uint64_to_usize(v___x_2091_);
v___x_2093_ = lean_usize_of_nat(v___x_2082_);
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_sub(v___x_2093_, v___x_2094_);
v___x_2096_ = lean_usize_land(v___x_2092_, v___x_2095_);
v___x_2097_ = lean_array_uget_borrowed(v_buckets_2081_, v___x_2096_);
lean_inc(v___x_2097_);
v___x_2098_ = l_Std_DHashMap_Internal_AssocList_get_x21___redArg(v_inst_2076_, v_inst_2078_, v_a_2080_, v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg___boxed(lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_m_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_2099_, v_inst_2100_, v_inst_2101_, v_m_2102_, v_a_2103_);
lean_dec_ref(v_m_2102_);
lean_dec(v_inst_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(lean_object* v_00_u03b1_2105_, lean_object* v_00_u03b2_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_m_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_2107_, v_inst_2108_, v_inst_2109_, v_m_2110_, v_a_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_m_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21(v_00_u03b1_2113_, v_00_u03b2_2114_, v_inst_2115_, v_inst_2116_, v_inst_2117_, v_m_2118_, v_a_2119_);
lean_dec_ref(v_m_2118_);
lean_dec(v_inst_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_m_2123_, lean_object* v_a_2124_, lean_object* v_b_2125_){
_start:
{
lean_object* v_size_2126_; lean_object* v_buckets_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; uint64_t v___x_2133_; uint64_t v_fold_2134_; uint64_t v___x_2135_; uint64_t v___x_2136_; uint64_t v___x_2137_; size_t v___x_2138_; size_t v___x_2139_; size_t v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; lean_object* v_bkt_2143_; lean_object* v___x_2144_; 
v_size_2126_ = lean_ctor_get(v_m_2123_, 0);
v_buckets_2127_ = lean_ctor_get(v_m_2123_, 1);
v___x_2128_ = lean_array_get_size(v_buckets_2127_);
lean_inc_ref(v_inst_2122_);
lean_inc_n(v_a_2124_, 2);
v___x_2129_ = lean_apply_1(v_inst_2122_, v_a_2124_);
v___x_2130_ = 32ULL;
v___x_2131_ = lean_unbox_uint64(v___x_2129_);
v___x_2132_ = lean_uint64_shift_right(v___x_2131_, v___x_2130_);
v___x_2133_ = lean_unbox_uint64(v___x_2129_);
lean_dec_ref(v___x_2129_);
v_fold_2134_ = lean_uint64_xor(v___x_2133_, v___x_2132_);
v___x_2135_ = 16ULL;
v___x_2136_ = lean_uint64_shift_right(v_fold_2134_, v___x_2135_);
v___x_2137_ = lean_uint64_xor(v_fold_2134_, v___x_2136_);
v___x_2138_ = lean_uint64_to_usize(v___x_2137_);
v___x_2139_ = lean_usize_of_nat(v___x_2128_);
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_sub(v___x_2139_, v___x_2140_);
v___x_2142_ = lean_usize_land(v___x_2138_, v___x_2141_);
v_bkt_2143_ = lean_array_uget_borrowed(v_buckets_2127_, v___x_2142_);
lean_inc(v_bkt_2143_);
v___x_2144_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_2121_, v_a_2124_, v_bkt_2143_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2167_; 
lean_inc_ref(v_buckets_2127_);
lean_inc(v_size_2126_);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_m_2123_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; 
v_unused_2168_ = lean_ctor_get(v_m_2123_, 1);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_m_2123_, 0);
lean_dec(v_unused_2169_);
v___x_2146_ = v_m_2123_;
v_isShared_2147_ = v_isSharedCheck_2167_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v_m_2123_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2167_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v_size_x27_2149_; lean_object* v___x_2150_; lean_object* v_buckets_x27_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2148_ = lean_unsigned_to_nat(1u);
v_size_x27_2149_ = lean_nat_add(v_size_2126_, v___x_2148_);
lean_dec(v_size_2126_);
lean_inc(v_bkt_2143_);
v___x_2150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2150_, 0, v_a_2124_);
lean_ctor_set(v___x_2150_, 1, v_b_2125_);
lean_ctor_set(v___x_2150_, 2, v_bkt_2143_);
v_buckets_x27_2151_ = lean_array_uset(v_buckets_2127_, v___x_2142_, v___x_2150_);
v___x_2152_ = lean_unsigned_to_nat(4u);
v___x_2153_ = lean_nat_mul(v_size_x27_2149_, v___x_2152_);
v___x_2154_ = lean_unsigned_to_nat(3u);
v___x_2155_ = lean_nat_div(v___x_2153_, v___x_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_array_get_size(v_buckets_x27_2151_);
v___x_2157_ = lean_nat_dec_le(v___x_2155_, v___x_2156_);
lean_dec(v___x_2155_);
if (v___x_2157_ == 0)
{
lean_object* v_val_2158_; lean_object* v___x_2160_; 
v_val_2158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2122_, v_buckets_x27_2151_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_val_2158_);
lean_ctor_set(v___x_2146_, 0, v_size_x27_2149_);
v___x_2160_ = v___x_2146_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_size_x27_2149_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_val_2158_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2144_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2164_; 
lean_dec_ref(v_inst_2122_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_buckets_x27_2151_);
lean_ctor_set(v___x_2146_, 0, v_size_x27_2149_);
v___x_2164_ = v___x_2146_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_size_x27_2149_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_buckets_x27_2151_);
v___x_2164_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2144_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
return v___x_2165_;
}
}
}
}
else
{
lean_object* v___x_2170_; 
lean_dec(v_b_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_inst_2122_);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2144_);
lean_ctor_set(v___x_2170_, 1, v_m_2123_);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_2171_, lean_object* v_00_u03b2_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_m_2175_, lean_object* v_a_2176_, lean_object* v_b_2177_){
_start:
{
lean_object* v_size_2178_; lean_object* v_buckets_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; uint64_t v___x_2182_; uint64_t v___x_2183_; uint64_t v___x_2184_; uint64_t v___x_2185_; uint64_t v_fold_2186_; uint64_t v___x_2187_; uint64_t v___x_2188_; uint64_t v___x_2189_; size_t v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; size_t v___x_2194_; lean_object* v_bkt_2195_; lean_object* v___x_2196_; 
v_size_2178_ = lean_ctor_get(v_m_2175_, 0);
v_buckets_2179_ = lean_ctor_get(v_m_2175_, 1);
v___x_2180_ = lean_array_get_size(v_buckets_2179_);
lean_inc_ref(v_inst_2174_);
lean_inc_n(v_a_2176_, 2);
v___x_2181_ = lean_apply_1(v_inst_2174_, v_a_2176_);
v___x_2182_ = 32ULL;
v___x_2183_ = lean_unbox_uint64(v___x_2181_);
v___x_2184_ = lean_uint64_shift_right(v___x_2183_, v___x_2182_);
v___x_2185_ = lean_unbox_uint64(v___x_2181_);
lean_dec_ref(v___x_2181_);
v_fold_2186_ = lean_uint64_xor(v___x_2185_, v___x_2184_);
v___x_2187_ = 16ULL;
v___x_2188_ = lean_uint64_shift_right(v_fold_2186_, v___x_2187_);
v___x_2189_ = lean_uint64_xor(v_fold_2186_, v___x_2188_);
v___x_2190_ = lean_uint64_to_usize(v___x_2189_);
v___x_2191_ = lean_usize_of_nat(v___x_2180_);
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_sub(v___x_2191_, v___x_2192_);
v___x_2194_ = lean_usize_land(v___x_2190_, v___x_2193_);
v_bkt_2195_ = lean_array_uget_borrowed(v_buckets_2179_, v___x_2194_);
lean_inc(v_bkt_2195_);
v___x_2196_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_2173_, v_a_2176_, v_bkt_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2219_; 
lean_inc_ref(v_buckets_2179_);
lean_inc(v_size_2178_);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_m_2175_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2220_ = lean_ctor_get(v_m_2175_, 1);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_m_2175_, 0);
lean_dec(v_unused_2221_);
v___x_2198_ = v_m_2175_;
v_isShared_2199_ = v_isSharedCheck_2219_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v_m_2175_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2219_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v_size_x27_2201_; lean_object* v___x_2202_; lean_object* v_buckets_x27_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v___x_2200_ = lean_unsigned_to_nat(1u);
v_size_x27_2201_ = lean_nat_add(v_size_2178_, v___x_2200_);
lean_dec(v_size_2178_);
lean_inc(v_bkt_2195_);
v___x_2202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2202_, 0, v_a_2176_);
lean_ctor_set(v___x_2202_, 1, v_b_2177_);
lean_ctor_set(v___x_2202_, 2, v_bkt_2195_);
v_buckets_x27_2203_ = lean_array_uset(v_buckets_2179_, v___x_2194_, v___x_2202_);
v___x_2204_ = lean_unsigned_to_nat(4u);
v___x_2205_ = lean_nat_mul(v_size_x27_2201_, v___x_2204_);
v___x_2206_ = lean_unsigned_to_nat(3u);
v___x_2207_ = lean_nat_div(v___x_2205_, v___x_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_array_get_size(v_buckets_x27_2203_);
v___x_2209_ = lean_nat_dec_le(v___x_2207_, v___x_2208_);
lean_dec(v___x_2207_);
if (v___x_2209_ == 0)
{
lean_object* v_val_2210_; lean_object* v___x_2212_; 
v_val_2210_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2174_, v_buckets_x27_2203_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v_val_2210_);
lean_ctor_set(v___x_2198_, 0, v_size_x27_2201_);
v___x_2212_ = v___x_2198_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_size_x27_2201_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_val_2210_);
v___x_2212_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2196_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2216_; 
lean_dec_ref(v_inst_2174_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v_buckets_x27_2203_);
lean_ctor_set(v___x_2198_, 0, v_size_x27_2201_);
v___x_2216_ = v___x_2198_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_size_x27_2201_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_buckets_x27_2203_);
v___x_2216_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2196_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
return v___x_2217_;
}
}
}
}
else
{
lean_object* v___x_2222_; 
lean_dec(v_b_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_inst_2174_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2196_);
lean_ctor_set(v___x_2222_, 1, v_m_2175_);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0(lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_x_2225_, lean_object* v_____s_2226_){
_start:
{
lean_object* v_fst_2227_; lean_object* v_snd_2228_; lean_object* v_r_2229_; lean_object* v___x_2230_; 
v_fst_2227_ = lean_ctor_get(v_x_2225_, 0);
lean_inc(v_fst_2227_);
v_snd_2228_ = lean_ctor_get(v_x_2225_, 1);
lean_inc(v_snd_2228_);
lean_dec_ref(v_x_2225_);
v_r_2229_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_2223_, v_inst_2224_, v_____s_2226_, v_fst_2227_, v_snd_2228_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_r_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object* v_inst_2231_, lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_m_2234_, lean_object* v_l_2235_){
_start:
{
lean_object* v___f_2236_; lean_object* v___x_2237_; 
v___f_2236_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2236_, 0, v_inst_2232_);
lean_closure_set(v___f_2236_, 1, v_inst_2233_);
v___x_2237_ = lean_apply_4(v_inst_2231_, lean_box(0), v_l_2235_, v_m_2234_, v___f_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany(lean_object* v_00_u03b1_2238_, lean_object* v_00_u03b2_2239_, lean_object* v_00_u03c1_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_m_2244_, lean_object* v_l_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2241_, v_inst_2242_, v_inst_2243_, v_m_2244_, v_l_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0(lean_object* v_inst_2247_, lean_object* v_inst_2248_, lean_object* v_a_2249_, lean_object* v_____s_2250_){
_start:
{
lean_object* v___x_2251_; lean_object* v_r_2252_; lean_object* v___x_2253_; 
v___x_2251_ = lean_box(0);
v_r_2252_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_2247_, v_inst_2248_, v_____s_2250_, v_a_2249_, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_r_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_m_2257_, lean_object* v_l_2258_){
_start:
{
lean_object* v___f_2259_; lean_object* v___x_2260_; 
v___f_2259_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2259_, 0, v_inst_2255_);
lean_closure_set(v___f_2259_, 1, v_inst_2256_);
v___x_2260_ = lean_apply_4(v_inst_2254_, lean_box(0), v_l_2258_, v_m_2257_, v___f_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_2261_, lean_object* v_00_u03c1_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_m_2266_, lean_object* v_l_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2263_, v_inst_2264_, v_inst_2265_, v_m_2266_, v_l_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_m_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_buckets_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint64_t v___x_2276_; uint64_t v___x_2277_; uint64_t v___x_2278_; uint64_t v___x_2279_; uint64_t v_fold_2280_; uint64_t v___x_2281_; uint64_t v___x_2282_; uint64_t v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_buckets_2273_ = lean_ctor_get(v_m_2271_, 1);
v___x_2274_ = lean_array_get_size(v_buckets_2273_);
lean_inc(v_a_2272_);
v___x_2275_ = lean_apply_1(v_inst_2270_, v_a_2272_);
v___x_2276_ = 32ULL;
v___x_2277_ = lean_unbox_uint64(v___x_2275_);
v___x_2278_ = lean_uint64_shift_right(v___x_2277_, v___x_2276_);
v___x_2279_ = lean_unbox_uint64(v___x_2275_);
lean_dec_ref(v___x_2275_);
v_fold_2280_ = lean_uint64_xor(v___x_2279_, v___x_2278_);
v___x_2281_ = 16ULL;
v___x_2282_ = lean_uint64_shift_right(v_fold_2280_, v___x_2281_);
v___x_2283_ = lean_uint64_xor(v_fold_2280_, v___x_2282_);
v___x_2284_ = lean_uint64_to_usize(v___x_2283_);
v___x_2285_ = lean_usize_of_nat(v___x_2274_);
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_sub(v___x_2285_, v___x_2286_);
v___x_2288_ = lean_usize_land(v___x_2284_, v___x_2287_);
v___x_2289_ = lean_array_uget_borrowed(v_buckets_2273_, v___x_2288_);
lean_inc(v___x_2289_);
v___x_2290_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_2269_, v_a_2272_, v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg___boxed(lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_m_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_2291_, v_inst_2292_, v_m_2293_, v_a_2294_);
lean_dec_ref(v_m_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(lean_object* v_00_u03b1_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_m_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_2298_, v_inst_2299_, v_m_2300_, v_a_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_00_u03b2_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_m_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f(v_00_u03b1_2303_, v_00_u03b2_2304_, v_inst_2305_, v_inst_2306_, v_m_2307_, v_a_2308_);
lean_dec_ref(v_m_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_m_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_buckets_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; uint64_t v___x_2319_; uint64_t v___x_2320_; uint64_t v_fold_2321_; uint64_t v___x_2322_; uint64_t v___x_2323_; uint64_t v___x_2324_; size_t v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_buckets_2314_ = lean_ctor_get(v_m_2312_, 1);
v___x_2315_ = lean_array_get_size(v_buckets_2314_);
lean_inc(v_a_2313_);
v___x_2316_ = lean_apply_1(v_inst_2311_, v_a_2313_);
v___x_2317_ = 32ULL;
v___x_2318_ = lean_unbox_uint64(v___x_2316_);
v___x_2319_ = lean_uint64_shift_right(v___x_2318_, v___x_2317_);
v___x_2320_ = lean_unbox_uint64(v___x_2316_);
lean_dec_ref(v___x_2316_);
v_fold_2321_ = lean_uint64_xor(v___x_2320_, v___x_2319_);
v___x_2322_ = 16ULL;
v___x_2323_ = lean_uint64_shift_right(v_fold_2321_, v___x_2322_);
v___x_2324_ = lean_uint64_xor(v_fold_2321_, v___x_2323_);
v___x_2325_ = lean_uint64_to_usize(v___x_2324_);
v___x_2326_ = lean_usize_of_nat(v___x_2315_);
v___x_2327_ = ((size_t)1ULL);
v___x_2328_ = lean_usize_sub(v___x_2326_, v___x_2327_);
v___x_2329_ = lean_usize_land(v___x_2325_, v___x_2328_);
v___x_2330_ = lean_array_uget_borrowed(v_buckets_2314_, v___x_2329_);
lean_inc(v___x_2330_);
v___x_2331_ = l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_2310_, v_a_2313_, v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg___boxed(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_m_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_2332_, v_inst_2333_, v_m_2334_, v_a_2335_);
lean_dec_ref(v_m_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey(lean_object* v_00_u03b1_2337_, lean_object* v_00_u03b2_2338_, lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_m_2341_, lean_object* v_a_2342_, lean_object* v_hma_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_2339_, v_inst_2340_, v_m_2341_, v_a_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___boxed(lean_object* v_00_u03b1_2345_, lean_object* v_00_u03b2_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_m_2349_, lean_object* v_a_2350_, lean_object* v_hma_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Std_DHashMap_Internal_Raw_u2080_getKey(v_00_u03b1_2345_, v_00_u03b2_2346_, v_inst_2347_, v_inst_2348_, v_m_2349_, v_a_2350_, v_hma_2351_);
lean_dec_ref(v_m_2349_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_m_2355_, lean_object* v_a_2356_, lean_object* v_fallback_2357_){
_start:
{
lean_object* v_buckets_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint64_t v___x_2361_; uint64_t v___x_2362_; uint64_t v___x_2363_; uint64_t v___x_2364_; uint64_t v_fold_2365_; uint64_t v___x_2366_; uint64_t v___x_2367_; uint64_t v___x_2368_; size_t v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_buckets_2358_ = lean_ctor_get(v_m_2355_, 1);
v___x_2359_ = lean_array_get_size(v_buckets_2358_);
lean_inc(v_a_2356_);
v___x_2360_ = lean_apply_1(v_inst_2354_, v_a_2356_);
v___x_2361_ = 32ULL;
v___x_2362_ = lean_unbox_uint64(v___x_2360_);
v___x_2363_ = lean_uint64_shift_right(v___x_2362_, v___x_2361_);
v___x_2364_ = lean_unbox_uint64(v___x_2360_);
lean_dec_ref(v___x_2360_);
v_fold_2365_ = lean_uint64_xor(v___x_2364_, v___x_2363_);
v___x_2366_ = 16ULL;
v___x_2367_ = lean_uint64_shift_right(v_fold_2365_, v___x_2366_);
v___x_2368_ = lean_uint64_xor(v_fold_2365_, v___x_2367_);
v___x_2369_ = lean_uint64_to_usize(v___x_2368_);
v___x_2370_ = lean_usize_of_nat(v___x_2359_);
v___x_2371_ = ((size_t)1ULL);
v___x_2372_ = lean_usize_sub(v___x_2370_, v___x_2371_);
v___x_2373_ = lean_usize_land(v___x_2369_, v___x_2372_);
v___x_2374_ = lean_array_uget_borrowed(v_buckets_2358_, v___x_2373_);
lean_inc(v___x_2374_);
v___x_2375_ = l_Std_DHashMap_Internal_AssocList_getKeyD___redArg(v_inst_2353_, v_a_2356_, v_fallback_2357_, v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg___boxed(lean_object* v_inst_2376_, lean_object* v_inst_2377_, lean_object* v_m_2378_, lean_object* v_a_2379_, lean_object* v_fallback_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_2376_, v_inst_2377_, v_m_2378_, v_a_2379_, v_fallback_2380_);
lean_dec(v_fallback_2380_);
lean_dec_ref(v_m_2378_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD(lean_object* v_00_u03b1_2382_, lean_object* v_00_u03b2_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_m_2386_, lean_object* v_a_2387_, lean_object* v_fallback_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_2384_, v_inst_2385_, v_m_2386_, v_a_2387_, v_fallback_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___boxed(lean_object* v_00_u03b1_2390_, lean_object* v_00_u03b2_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_m_2394_, lean_object* v_a_2395_, lean_object* v_fallback_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD(v_00_u03b1_2390_, v_00_u03b2_2391_, v_inst_2392_, v_inst_2393_, v_m_2394_, v_a_2395_, v_fallback_2396_);
lean_dec(v_fallback_2396_);
lean_dec_ref(v_m_2394_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_m_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_buckets_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint64_t v___x_2406_; uint64_t v___x_2407_; uint64_t v___x_2408_; uint64_t v___x_2409_; uint64_t v_fold_2410_; uint64_t v___x_2411_; uint64_t v___x_2412_; uint64_t v___x_2413_; size_t v___x_2414_; size_t v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_buckets_2403_ = lean_ctor_get(v_m_2401_, 1);
v___x_2404_ = lean_array_get_size(v_buckets_2403_);
lean_inc(v_a_2402_);
v___x_2405_ = lean_apply_1(v_inst_2399_, v_a_2402_);
v___x_2406_ = 32ULL;
v___x_2407_ = lean_unbox_uint64(v___x_2405_);
v___x_2408_ = lean_uint64_shift_right(v___x_2407_, v___x_2406_);
v___x_2409_ = lean_unbox_uint64(v___x_2405_);
lean_dec_ref(v___x_2405_);
v_fold_2410_ = lean_uint64_xor(v___x_2409_, v___x_2408_);
v___x_2411_ = 16ULL;
v___x_2412_ = lean_uint64_shift_right(v_fold_2410_, v___x_2411_);
v___x_2413_ = lean_uint64_xor(v_fold_2410_, v___x_2412_);
v___x_2414_ = lean_uint64_to_usize(v___x_2413_);
v___x_2415_ = lean_usize_of_nat(v___x_2404_);
v___x_2416_ = ((size_t)1ULL);
v___x_2417_ = lean_usize_sub(v___x_2415_, v___x_2416_);
v___x_2418_ = lean_usize_land(v___x_2414_, v___x_2417_);
v___x_2419_ = lean_array_uget_borrowed(v_buckets_2403_, v___x_2418_);
lean_inc(v___x_2419_);
v___x_2420_ = l_Std_DHashMap_Internal_AssocList_getKey_x21___redArg(v_inst_2398_, v_inst_2400_, v_a_2402_, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg___boxed(lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_m_2424_, lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_2421_, v_inst_2422_, v_inst_2423_, v_m_2424_, v_a_2425_);
lean_dec_ref(v_m_2424_);
lean_dec(v_inst_2423_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(lean_object* v_00_u03b1_2427_, lean_object* v_00_u03b2_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_m_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_2429_, v_inst_2430_, v_inst_2431_, v_m_2432_, v_a_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_00_u03b2_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_m_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21(v_00_u03b1_2435_, v_00_u03b2_2436_, v_inst_2437_, v_inst_2438_, v_inst_2439_, v_m_2440_, v_a_2441_);
lean_dec_ref(v_m_2440_);
lean_dec(v_inst_2439_);
return v_res_2442_;
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
