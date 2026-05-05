// Lean compiler output
// Module: Std.Data.DHashMap.Internal.Model
// Imports: public import Init.Data.Array.TakeDrop public import Std.Data.DHashMap.Basic import all Std.Data.DHashMap.Internal.Defs public import Std.Data.DHashMap.Internal.HashesTo public import Std.Data.DHashMap.Internal.AssocList.Lemmas import Init.Data.Array.Bootstrap import Init.Data.UInt.Lemmas
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
lean_object* l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getCast___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_getKey___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_erase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_toListModel___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateBucket___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateBucket(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateAllBuckets___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateAllBuckets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value;
static const lean_closure_object l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__10_value)} };
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket___redArg(lean_object* v_inst_1_, lean_object* v_self_2_, lean_object* v_k_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint64_t v___x_6_; uint64_t v___x_7_; uint64_t v___x_8_; uint64_t v___x_9_; uint64_t v_fold_10_; uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v___x_13_; size_t v___x_14_; size_t v___x_15_; size_t v___x_16_; size_t v___x_17_; size_t v___x_18_; lean_object* v___x_19_; 
v___x_4_ = lean_array_get_size(v_self_2_);
v___x_5_ = lean_apply_1(v_inst_1_, v_k_3_);
v___x_6_ = 32ULL;
v___x_7_ = lean_unbox_uint64(v___x_5_);
v___x_8_ = lean_uint64_shift_right(v___x_7_, v___x_6_);
v___x_9_ = lean_unbox_uint64(v___x_5_);
lean_dec_ref(v___x_5_);
v_fold_10_ = lean_uint64_xor(v___x_9_, v___x_8_);
v___x_11_ = 16ULL;
v___x_12_ = lean_uint64_shift_right(v_fold_10_, v___x_11_);
v___x_13_ = lean_uint64_xor(v_fold_10_, v___x_12_);
v___x_14_ = lean_uint64_to_usize(v___x_13_);
v___x_15_ = lean_usize_of_nat(v___x_4_);
v___x_16_ = ((size_t)1ULL);
v___x_17_ = lean_usize_sub(v___x_15_, v___x_16_);
v___x_18_ = lean_usize_land(v___x_14_, v___x_17_);
v___x_19_ = lean_array_uget_borrowed(v_self_2_, v___x_18_);
lean_inc(v___x_19_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket___redArg___boxed(lean_object* v_inst_20_, lean_object* v_self_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_20_, v_self_21_, v_k_22_);
lean_dec_ref(v_self_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_inst_26_, lean_object* v_self_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_26_, v_self_27_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_bucket___boxed(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_self_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_DHashMap_Internal_bucket(v_00_u03b1_31_, v_00_u03b2_32_, v_inst_33_, v_self_34_, v_h_35_, v_k_36_);
lean_dec_ref(v_self_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateBucket___redArg(lean_object* v_inst_38_, lean_object* v_self_39_, lean_object* v_k_40_, lean_object* v_f_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; uint64_t v_fold_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; size_t v___x_52_; size_t v___x_53_; size_t v___x_54_; size_t v___x_55_; size_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_42_ = lean_array_get_size(v_self_39_);
v___x_43_ = lean_apply_1(v_inst_38_, v_k_40_);
v___x_44_ = 32ULL;
v___x_45_ = lean_unbox_uint64(v___x_43_);
v___x_46_ = lean_uint64_shift_right(v___x_45_, v___x_44_);
v___x_47_ = lean_unbox_uint64(v___x_43_);
lean_dec_ref(v___x_43_);
v_fold_48_ = lean_uint64_xor(v___x_47_, v___x_46_);
v___x_49_ = 16ULL;
v___x_50_ = lean_uint64_shift_right(v_fold_48_, v___x_49_);
v___x_51_ = lean_uint64_xor(v_fold_48_, v___x_50_);
v___x_52_ = lean_uint64_to_usize(v___x_51_);
v___x_53_ = lean_usize_of_nat(v___x_42_);
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_sub(v___x_53_, v___x_54_);
v___x_56_ = lean_usize_land(v___x_52_, v___x_55_);
v___x_57_ = lean_array_uget_borrowed(v_self_39_, v___x_56_);
lean_inc(v___x_57_);
v___x_58_ = lean_apply_1(v_f_41_, v___x_57_);
v___x_59_ = lean_array_uset(v_self_39_, v___x_56_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateBucket(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_, lean_object* v_inst_62_, lean_object* v_self_63_, lean_object* v_h_64_, lean_object* v_k_65_, lean_object* v_f_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_62_, v_self_63_, v_k_65_, v_f_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(lean_object* v_f_68_, size_t v_sz_69_, size_t v_i_70_, lean_object* v_bs_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_usize_dec_lt(v_i_70_, v_sz_69_);
if (v___x_72_ == 0)
{
lean_dec_ref(v_f_68_);
return v_bs_71_;
}
else
{
lean_object* v_v_73_; lean_object* v___x_74_; lean_object* v_bs_x27_75_; lean_object* v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v___x_79_; 
v_v_73_ = lean_array_uget(v_bs_71_, v_i_70_);
v___x_74_ = lean_unsigned_to_nat(0u);
v_bs_x27_75_ = lean_array_uset(v_bs_71_, v_i_70_, v___x_74_);
lean_inc_ref(v_f_68_);
v___x_76_ = lean_apply_1(v_f_68_, v_v_73_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_add(v_i_70_, v___x_77_);
v___x_79_ = lean_array_uset(v_bs_x27_75_, v_i_70_, v___x_76_);
v_i_70_ = v___x_78_;
v_bs_71_ = v___x_79_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg___boxed(lean_object* v_f_81_, lean_object* v_sz_82_, lean_object* v_i_83_, lean_object* v_bs_84_){
_start:
{
size_t v_sz_boxed_85_; size_t v_i_boxed_86_; lean_object* v_res_87_; 
v_sz_boxed_85_ = lean_unbox_usize(v_sz_82_);
lean_dec(v_sz_82_);
v_i_boxed_86_ = lean_unbox_usize(v_i_83_);
lean_dec(v_i_83_);
v_res_87_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_81_, v_sz_boxed_85_, v_i_boxed_86_, v_bs_84_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateAllBuckets___redArg(lean_object* v_self_88_, lean_object* v_f_89_){
_start:
{
size_t v_sz_90_; size_t v___x_91_; lean_object* v___x_92_; 
v_sz_90_ = lean_array_size(v_self_88_);
v___x_91_ = ((size_t)0ULL);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_89_, v_sz_90_, v___x_91_, v_self_88_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateAllBuckets(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_00_u03b4_95_, lean_object* v_self_96_, lean_object* v_f_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_self_96_, v_f_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_00_u03b4_101_, lean_object* v_f_102_, size_t v_sz_103_, size_t v_i_104_, lean_object* v_bs_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_102_, v_sz_103_, v_i_104_, v_bs_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_00_u03b4_109_, lean_object* v_f_110_, lean_object* v_sz_111_, lean_object* v_i_112_, lean_object* v_bs_113_){
_start:
{
size_t v_sz_boxed_114_; size_t v_i_boxed_115_; lean_object* v_res_116_; 
v_sz_boxed_114_ = lean_unbox_usize(v_sz_111_);
lean_dec(v_sz_111_);
v_i_boxed_115_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_res_116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(v_00_u03b1_107_, v_00_u03b2_108_, v_00_u03b4_109_, v_f_110_, v_sz_boxed_114_, v_i_boxed_115_, v_bs_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(lean_object* v_as_117_, size_t v_i_118_, size_t v_stop_119_, lean_object* v_b_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = lean_usize_dec_eq(v_i_118_, v_stop_119_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; size_t v___x_125_; size_t v___x_126_; 
v___x_122_ = lean_array_uget_borrowed(v_as_117_, v_i_118_);
v___x_123_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_122_);
v___x_124_ = lean_nat_add(v_b_120_, v___x_123_);
lean_dec(v___x_123_);
lean_dec(v_b_120_);
v___x_125_ = ((size_t)1ULL);
v___x_126_ = lean_usize_add(v_i_118_, v___x_125_);
v_i_118_ = v___x_126_;
v_b_120_ = v___x_124_;
goto _start;
}
else
{
return v_b_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg___boxed(lean_object* v_as_128_, lean_object* v_i_129_, lean_object* v_stop_130_, lean_object* v_b_131_){
_start:
{
size_t v_i_boxed_132_; size_t v_stop_boxed_133_; lean_object* v_res_134_; 
v_i_boxed_132_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_stop_boxed_133_ = lean_unbox_usize(v_stop_130_);
lean_dec(v_stop_130_);
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_128_, v_i_boxed_132_, v_stop_boxed_133_, v_b_131_);
lean_dec_ref(v_as_128_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize___redArg(lean_object* v_self_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_array_get_size(v_self_135_);
v___x_138_ = lean_nat_dec_lt(v___x_136_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_136_);
lean_ctor_set(v___x_139_, 1, v_self_135_);
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = lean_nat_dec_le(v___x_137_, v___x_137_);
if (v___x_140_ == 0)
{
if (v___x_138_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_136_);
lean_ctor_set(v___x_141_, 1, v_self_135_);
return v___x_141_;
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_137_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_135_, v___x_142_, v___x_143_, v___x_136_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_self_135_);
return v___x_145_;
}
}
else
{
size_t v___x_146_; size_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_137_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_135_, v___x_146_, v___x_147_, v___x_136_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_self_135_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize(lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_self_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_self_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_as_156_, size_t v_i_157_, size_t v_stop_158_, lean_object* v_b_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_156_, v_i_157_, v_stop_158_, v_b_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___boxed(lean_object* v_00_u03b1_161_, lean_object* v_00_u03b2_162_, lean_object* v_as_163_, lean_object* v_i_164_, lean_object* v_stop_165_, lean_object* v_b_166_){
_start:
{
size_t v_i_boxed_167_; size_t v_stop_boxed_168_; lean_object* v_res_169_; 
v_i_boxed_167_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_stop_boxed_168_ = lean_unbox_usize(v_stop_165_);
lean_dec(v_stop_165_);
v_res_169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(v_00_u03b1_161_, v_00_u03b2_162_, v_as_163_, v_i_boxed_167_, v_stop_boxed_168_, v_b_166_);
lean_dec_ref(v_as_163_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0(lean_object* v_inst_170_, lean_object* v_a_171_, lean_object* v_b_172_, lean_object* v_l_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_170_, v_a_171_, v_b_172_, v_l_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_m_177_, lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_size_180_; lean_object* v_buckets_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_190_; 
v_size_180_ = lean_ctor_get(v_m_177_, 0);
v_buckets_181_ = lean_ctor_get(v_m_177_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_m_177_);
if (v_isSharedCheck_190_ == 0)
{
v___x_183_ = v_m_177_;
v_isShared_184_ = v_isSharedCheck_190_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_buckets_181_);
lean_inc(v_size_180_);
lean_dec(v_m_177_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_190_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___f_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
lean_inc(v_a_178_);
v___f_185_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_185_, 0, v_inst_175_);
lean_closure_set(v___f_185_, 1, v_a_178_);
lean_closure_set(v___f_185_, 2, v_b_179_);
v___x_186_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_176_, v_buckets_181_, v_a_178_, v___f_185_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_size_180_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_m_195_, lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(v_inst_193_, v_inst_194_, v_m_195_, v_a_196_, v_b_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0(lean_object* v_a_199_, lean_object* v_b_200_, lean_object* v_l_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_202_, 0, v_a_199_);
lean_ctor_set(v___x_202_, 1, v_b_200_);
lean_ctor_set(v___x_202_, 2, v_l_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(lean_object* v_inst_203_, lean_object* v_m_204_, lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
lean_object* v_size_207_; lean_object* v_buckets_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_219_; 
v_size_207_ = lean_ctor_get(v_m_204_, 0);
v_buckets_208_ = lean_ctor_get(v_m_204_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_m_204_);
if (v_isSharedCheck_219_ == 0)
{
v___x_210_ = v_m_204_;
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_buckets_208_);
lean_inc(v_size_207_);
lean_dec(v_m_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_219_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc(v_a_205_);
v___f_212_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0), 3, 2);
lean_closure_set(v___f_212_, 0, v_a_205_);
lean_closure_set(v___f_212_, 1, v_b_206_);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v_size_207_, v___x_213_);
lean_dec(v_size_207_);
v___x_215_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_203_, v_buckets_208_, v_a_205_, v___f_212_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v___x_215_);
lean_ctor_set(v___x_210_, 0, v___x_214_);
v___x_217_ = v___x_210_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_m_224_, lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_223_, v_m_224_, v_a_225_, v_b_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___boxed(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_m_232_, lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(v_00_u03b1_228_, v_00_u03b2_229_, v_inst_230_, v_inst_231_, v_m_232_, v_a_233_, v_b_234_);
lean_dec_ref(v_inst_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_m_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_buckets_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_buckets_240_ = lean_ctor_get(v_m_238_, 1);
lean_inc(v_a_239_);
v___x_241_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_237_, v_buckets_240_, v_a_239_);
v___x_242_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_236_, v_a_239_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_243_, v_inst_244_, v_m_245_, v_a_246_);
lean_dec_ref(v_m_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(lean_object* v_00_u03b1_248_, lean_object* v_00_u03b2_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_m_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_250_, v_inst_252_, v_m_253_, v_a_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_m_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(v_00_u03b1_256_, v_00_u03b2_257_, v_inst_258_, v_inst_259_, v_inst_260_, v_m_261_, v_a_262_);
lean_dec_ref(v_m_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_m_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_buckets_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v_buckets_268_ = lean_ctor_get(v_m_266_, 1);
lean_inc(v_a_267_);
v___x_269_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_265_, v_buckets_268_, v_a_267_);
v___x_270_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_264_, v_a_267_, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_m_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_271_, v_inst_272_, v_m_273_, v_a_274_);
lean_dec_ref(v_m_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_m_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_278_, v_inst_279_, v_m_280_, v_a_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_m_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(v_00_u03b1_283_, v_00_u03b2_284_, v_inst_285_, v_inst_286_, v_m_287_, v_a_288_);
lean_dec_ref(v_m_287_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_m_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_buckets_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_buckets_294_ = lean_ctor_get(v_m_292_, 1);
lean_inc(v_a_293_);
v___x_295_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_291_, v_buckets_294_, v_a_293_);
v___x_296_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_290_, v_a_293_, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_m_299_, lean_object* v_a_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_297_, v_inst_298_, v_m_299_, v_a_300_);
lean_dec_ref(v_m_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_object* v_00_u03b1_303_, lean_object* v_00_u03b2_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_m_307_, lean_object* v_a_308_){
_start:
{
uint8_t v___x_309_; 
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_305_, v_inst_306_, v_m_307_, v_a_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___boxed(lean_object* v_00_u03b1_310_, lean_object* v_00_u03b2_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_m_314_, lean_object* v_a_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(v_00_u03b1_310_, v_00_u03b2_311_, v_inst_312_, v_inst_313_, v_m_314_, v_a_315_);
lean_dec_ref(v_m_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_m_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_buckets_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_buckets_322_ = lean_ctor_get(v_m_320_, 1);
lean_inc(v_a_321_);
v___x_323_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_319_, v_buckets_322_, v_a_321_);
v___x_324_ = l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_318_, v_a_321_, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(v_inst_325_, v_inst_326_, v_m_327_, v_a_328_);
lean_dec_ref(v_m_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_m_335_, lean_object* v_a_336_, lean_object* v_h_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(v_inst_332_, v_inst_334_, v_m_335_, v_a_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_m_344_, lean_object* v_a_345_, lean_object* v_h_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098(v_00_u03b1_339_, v_00_u03b2_340_, v_inst_341_, v_inst_342_, v_inst_343_, v_m_344_, v_a_345_, v_h_346_);
lean_dec_ref(v_m_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_buckets_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_buckets_352_ = lean_ctor_get(v_m_350_, 1);
lean_inc(v_a_351_);
v___x_353_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_349_, v_buckets_352_, v_a_351_);
v___x_354_ = l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_348_, v_a_351_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_m_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(v_inst_355_, v_inst_356_, v_m_357_, v_a_358_);
lean_dec_ref(v_m_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(lean_object* v_00_u03b1_360_, lean_object* v_00_u03b2_361_, lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_m_364_, lean_object* v_a_365_, lean_object* v_h_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(v_inst_362_, v_inst_363_, v_m_364_, v_a_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_m_372_, lean_object* v_a_373_, lean_object* v_h_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(v_00_u03b1_368_, v_00_u03b2_369_, v_inst_370_, v_inst_371_, v_m_372_, v_a_373_, v_h_374_);
lean_dec_ref(v_m_372_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_m_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_buckets_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_buckets_380_ = lean_ctor_get(v_m_378_, 1);
lean_inc(v_a_379_);
v___x_381_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_377_, v_buckets_380_, v_a_379_);
v___x_382_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_376_, v_a_379_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_383_, v_inst_384_, v_m_385_, v_a_386_);
lean_dec_ref(v_m_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_390_, v_inst_391_, v_m_392_, v_a_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(v_00_u03b1_395_, v_00_u03b2_396_, v_inst_397_, v_inst_398_, v_m_399_, v_a_400_);
lean_dec_ref(v_m_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_m_404_, lean_object* v_a_405_, lean_object* v_fallback_406_){
_start:
{
lean_object* v_buckets_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_buckets_407_ = lean_ctor_get(v_m_404_, 1);
lean_inc(v_a_405_);
v___x_408_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_403_, v_buckets_407_, v_a_405_);
v___x_409_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(v_inst_402_, v_a_405_, v_fallback_406_, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg___boxed(lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_m_412_, lean_object* v_a_413_, lean_object* v_fallback_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(v_inst_410_, v_inst_411_, v_m_412_, v_a_413_, v_fallback_414_);
lean_dec_ref(v_fallback_414_);
lean_dec_ref(v_m_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_m_420_, lean_object* v_a_421_, lean_object* v_fallback_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(v_inst_418_, v_inst_419_, v_m_420_, v_a_421_, v_fallback_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___boxed(lean_object* v_00_u03b1_424_, lean_object* v_00_u03b2_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_a_429_, lean_object* v_fallback_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(v_00_u03b1_424_, v_00_u03b2_425_, v_inst_426_, v_inst_427_, v_m_428_, v_a_429_, v_fallback_430_);
lean_dec_ref(v_fallback_430_);
lean_dec_ref(v_m_428_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_m_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_buckets_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_buckets_437_ = lean_ctor_get(v_m_435_, 1);
lean_inc(v_a_436_);
v___x_438_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_433_, v_buckets_437_, v_a_436_);
v___x_439_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(v_inst_432_, v_a_436_, v_inst_434_, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(v_inst_440_, v_inst_441_, v_inst_442_, v_m_443_, v_a_444_);
lean_dec_ref(v_m_443_);
lean_dec_ref(v_inst_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_m_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(v_inst_448_, v_inst_449_, v_inst_450_, v_m_451_, v_a_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_m_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(v_00_u03b1_454_, v_00_u03b2_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_m_459_, v_a_460_);
lean_dec_ref(v_m_459_);
lean_dec_ref(v_inst_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_m_464_, lean_object* v_a_465_, lean_object* v_fallback_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_462_, v_inst_463_, v_m_464_, v_a_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_inc(v_fallback_466_);
return v_fallback_466_;
}
else
{
lean_object* v_val_468_; 
v_val_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_468_);
lean_dec_ref(v___x_467_);
return v_val_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_m_471_, lean_object* v_a_472_, lean_object* v_fallback_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(v_inst_469_, v_inst_470_, v_m_471_, v_a_472_, v_fallback_473_);
lean_dec(v_fallback_473_);
lean_dec_ref(v_m_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_m_480_, lean_object* v_a_481_, lean_object* v_fallback_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(v_inst_477_, v_inst_479_, v_m_480_, v_a_481_, v_fallback_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___boxed(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(v_00_u03b1_484_, v_00_u03b2_485_, v_inst_486_, v_inst_487_, v_inst_488_, v_m_489_, v_a_490_, v_fallback_491_);
lean_dec(v_fallback_491_);
lean_dec_ref(v_m_489_);
return v_res_492_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_496_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2));
v___x_497_ = lean_unsigned_to_nat(14u);
v___x_498_ = lean_unsigned_to_nat(22u);
v___x_499_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1));
v___x_500_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0));
v___x_501_ = l_mkPanicMessageWithDecl(v___x_500_, v___x_499_, v___x_498_, v___x_497_, v___x_496_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_m_504_, lean_object* v_a_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_502_, v_inst_503_, v_m_504_, v_a_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_509_ = l_panic___redArg(v_inst_506_, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_val_510_; 
v_val_510_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_val_510_);
lean_dec_ref(v___x_507_);
return v_val_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_m_513_, lean_object* v_a_514_, lean_object* v_inst_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(v_inst_511_, v_inst_512_, v_m_513_, v_a_514_, v_inst_515_);
lean_dec(v_inst_515_);
lean_dec_ref(v_m_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_m_522_, lean_object* v_a_523_, lean_object* v_inst_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(v_inst_519_, v_inst_521_, v_m_522_, v_a_523_, v_inst_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___boxed(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_m_531_, lean_object* v_a_532_, lean_object* v_inst_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(v_00_u03b1_526_, v_00_u03b2_527_, v_inst_528_, v_inst_529_, v_inst_530_, v_m_531_, v_a_532_, v_inst_533_);
lean_dec(v_inst_533_);
lean_dec_ref(v_m_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_m_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_buckets_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_buckets_539_ = lean_ctor_get(v_m_537_, 1);
lean_inc(v_a_538_);
v___x_540_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_536_, v_buckets_539_, v_a_538_);
v___x_541_ = l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_535_, v_a_538_, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_m_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(v_inst_542_, v_inst_543_, v_m_544_, v_a_545_);
lean_dec_ref(v_m_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(lean_object* v_00_u03b1_547_, lean_object* v_00_u03b2_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_m_551_, lean_object* v_a_552_, lean_object* v_h_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(v_inst_549_, v_inst_550_, v_m_551_, v_a_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_m_559_, lean_object* v_a_560_, lean_object* v_h_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(v_00_u03b1_555_, v_00_u03b2_556_, v_inst_557_, v_inst_558_, v_m_559_, v_a_560_, v_h_561_);
lean_dec_ref(v_m_559_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_m_565_, lean_object* v_a_566_, lean_object* v_fallback_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_563_, v_inst_564_, v_m_565_, v_a_566_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_inc(v_fallback_567_);
return v_fallback_567_;
}
else
{
lean_object* v_val_569_; 
v_val_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v___x_568_);
return v_val_569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_m_572_, lean_object* v_a_573_, lean_object* v_fallback_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(v_inst_570_, v_inst_571_, v_m_572_, v_a_573_, v_fallback_574_);
lean_dec(v_fallback_574_);
lean_dec_ref(v_m_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(lean_object* v_00_u03b1_576_, lean_object* v_00_u03b2_577_, lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_m_580_, lean_object* v_a_581_, lean_object* v_fallback_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(v_inst_578_, v_inst_579_, v_m_580_, v_a_581_, v_fallback_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_m_588_, lean_object* v_a_589_, lean_object* v_fallback_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(v_00_u03b1_584_, v_00_u03b2_585_, v_inst_586_, v_inst_587_, v_m_588_, v_a_589_, v_fallback_590_);
lean_dec(v_fallback_590_);
lean_dec_ref(v_m_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_m_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_592_, v_inst_593_, v_m_595_, v_a_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_599_ = l_panic___redArg(v_inst_594_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v_val_600_; 
v_val_600_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_600_);
lean_dec_ref(v___x_597_);
return v_val_600_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(v_inst_601_, v_inst_602_, v_inst_603_, v_m_604_, v_a_605_);
lean_dec_ref(v_m_604_);
lean_dec(v_inst_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(lean_object* v_00_u03b1_607_, lean_object* v_00_u03b2_608_, lean_object* v_inst_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_m_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(v_inst_609_, v_inst_610_, v_inst_611_, v_m_612_, v_a_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_615_, lean_object* v_00_u03b2_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(v_00_u03b1_615_, v_00_u03b2_616_, v_inst_617_, v_inst_618_, v_inst_619_, v_m_620_, v_a_621_);
lean_dec_ref(v_m_620_);
lean_dec(v_inst_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(lean_object* v_inst_623_, lean_object* v_inst_624_, lean_object* v_m_625_, lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
uint8_t v___x_628_; 
lean_inc(v_a_626_);
lean_inc_ref(v_inst_624_);
lean_inc_ref(v_inst_623_);
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_623_, v_inst_624_, v_m_625_, v_a_626_);
if (v___x_628_ == 0)
{
lean_object* v_val_629_; lean_object* v_size_630_; lean_object* v_buckets_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
lean_dec_ref(v_inst_623_);
lean_inc_ref(v_inst_624_);
v_val_629_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_624_, v_m_625_, v_a_626_, v_b_627_);
v_size_630_ = lean_ctor_get(v_val_629_, 0);
lean_inc(v_size_630_);
v_buckets_631_ = lean_ctor_get(v_val_629_, 1);
lean_inc_ref(v_buckets_631_);
v___x_632_ = lean_unsigned_to_nat(4u);
v___x_633_ = lean_nat_mul(v_size_630_, v___x_632_);
v___x_634_ = lean_unsigned_to_nat(3u);
v___x_635_ = lean_nat_div(v___x_633_, v___x_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_array_get_size(v_buckets_631_);
v___x_637_ = lean_nat_dec_le(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_isSharedCheck_645_ = !lean_is_exclusive(v_val_629_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; lean_object* v_unused_647_; 
v_unused_646_ = lean_ctor_get(v_val_629_, 1);
lean_dec(v_unused_646_);
v_unused_647_ = lean_ctor_get(v_val_629_, 0);
lean_dec(v_unused_647_);
v___x_639_ = v_val_629_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_dec(v_val_629_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_val_641_; lean_object* v___x_643_; 
v_val_641_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_624_, v_buckets_631_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_val_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_size_630_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_val_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_dec_ref(v_buckets_631_);
lean_dec(v_size_630_);
lean_dec_ref(v_inst_624_);
return v_val_629_;
}
}
else
{
lean_object* v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(v_inst_623_, v_inst_624_, v_m_625_, v_a_626_, v_b_627_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(v_inst_651_, v_inst_652_, v_m_653_, v_a_654_, v_b_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_m_659_, lean_object* v_a_660_, lean_object* v_b_661_){
_start:
{
uint8_t v___x_662_; 
lean_inc(v_a_660_);
lean_inc_ref(v_inst_658_);
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_657_, v_inst_658_, v_m_659_, v_a_660_);
if (v___x_662_ == 0)
{
lean_object* v_val_663_; lean_object* v_size_664_; lean_object* v_buckets_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
lean_inc_ref(v_inst_658_);
v_val_663_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_658_, v_m_659_, v_a_660_, v_b_661_);
v_size_664_ = lean_ctor_get(v_val_663_, 0);
lean_inc(v_size_664_);
v_buckets_665_ = lean_ctor_get(v_val_663_, 1);
lean_inc_ref(v_buckets_665_);
v___x_666_ = lean_unsigned_to_nat(4u);
v___x_667_ = lean_nat_mul(v_size_664_, v___x_666_);
v___x_668_ = lean_unsigned_to_nat(3u);
v___x_669_ = lean_nat_div(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_array_get_size(v_buckets_665_);
v___x_671_ = lean_nat_dec_le(v___x_669_, v___x_670_);
lean_dec(v___x_669_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_isSharedCheck_679_ = !lean_is_exclusive(v_val_663_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; lean_object* v_unused_681_; 
v_unused_680_ = lean_ctor_get(v_val_663_, 1);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_val_663_, 0);
lean_dec(v_unused_681_);
v___x_673_ = v_val_663_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_dec(v_val_663_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_val_675_; lean_object* v___x_677_; 
v_val_675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_658_, v_buckets_665_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_val_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_size_664_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_val_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_dec_ref(v_buckets_665_);
lean_dec(v_size_664_);
lean_dec_ref(v_inst_658_);
return v_val_663_;
}
}
else
{
lean_dec(v_b_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_inst_658_);
return v_m_659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_m_686_, lean_object* v_a_687_, lean_object* v_b_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(v_inst_684_, v_inst_685_, v_m_686_, v_a_687_, v_b_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0(lean_object* v_inst_690_, lean_object* v_a_691_, lean_object* v_l_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_690_, v_a_691_, v_l_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_m_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_size_698_; lean_object* v_buckets_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_710_; 
v_size_698_ = lean_ctor_get(v_m_696_, 0);
v_buckets_699_ = lean_ctor_get(v_m_696_, 1);
v_isSharedCheck_710_ = !lean_is_exclusive(v_m_696_);
if (v_isSharedCheck_710_ == 0)
{
v___x_701_ = v_m_696_;
v_isShared_702_ = v_isSharedCheck_710_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_buckets_699_);
lean_inc(v_size_698_);
lean_dec(v_m_696_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_710_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
lean_inc(v_a_697_);
v___f_703_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_703_, 0, v_inst_694_);
lean_closure_set(v___f_703_, 1, v_a_697_);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_sub(v_size_698_, v___x_704_);
lean_dec(v_size_698_);
v___x_706_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_695_, v_buckets_699_, v_a_697_, v___f_703_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v___x_706_);
lean_ctor_set(v___x_701_, 0, v___x_705_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux(lean_object* v_00_u03b1_711_, lean_object* v_00_u03b2_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_m_715_, lean_object* v_a_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(v_inst_713_, v_inst_714_, v_m_715_, v_a_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_m_720_, lean_object* v_a_721_){
_start:
{
uint8_t v___x_722_; 
lean_inc(v_a_721_);
lean_inc_ref(v_inst_719_);
lean_inc_ref(v_inst_718_);
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_718_, v_inst_719_, v_m_720_, v_a_721_);
if (v___x_722_ == 0)
{
lean_dec(v_a_721_);
lean_dec_ref(v_inst_719_);
lean_dec_ref(v_inst_718_);
return v_m_720_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(v_inst_718_, v_inst_719_, v_m_720_, v_a_721_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(v_inst_726_, v_inst_727_, v_m_728_, v_a_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0(lean_object* v_inst_731_, lean_object* v_a_732_, lean_object* v_f_733_, lean_object* v_l_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(v_inst_731_, v_a_732_, v_f_733_, v_l_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_m_738_, lean_object* v_a_739_, lean_object* v_f_740_){
_start:
{
uint8_t v___x_741_; 
lean_inc(v_a_739_);
lean_inc_ref(v_inst_737_);
lean_inc_ref(v_inst_736_);
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_736_, v_inst_737_, v_m_738_, v_a_739_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec_ref(v_inst_736_);
v___x_742_ = lean_box(0);
v___x_743_ = lean_apply_1(v_f_740_, v___x_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec(v_a_739_);
lean_dec_ref(v_inst_737_);
return v_m_738_;
}
else
{
lean_object* v_val_744_; lean_object* v_val_745_; lean_object* v_size_746_; lean_object* v_buckets_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref(v___x_743_);
lean_inc_ref(v_inst_737_);
v_val_745_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_737_, v_m_738_, v_a_739_, v_val_744_);
v_size_746_ = lean_ctor_get(v_val_745_, 0);
lean_inc(v_size_746_);
v_buckets_747_ = lean_ctor_get(v_val_745_, 1);
lean_inc_ref(v_buckets_747_);
v___x_748_ = lean_unsigned_to_nat(4u);
v___x_749_ = lean_nat_mul(v_size_746_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(3u);
v___x_751_ = lean_nat_div(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_array_get_size(v_buckets_747_);
v___x_753_ = lean_nat_dec_le(v___x_751_, v___x_752_);
lean_dec(v___x_751_);
if (v___x_753_ == 0)
{
lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_isSharedCheck_761_ = !lean_is_exclusive(v_val_745_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; lean_object* v_unused_763_; 
v_unused_762_ = lean_ctor_get(v_val_745_, 1);
lean_dec(v_unused_762_);
v_unused_763_ = lean_ctor_get(v_val_745_, 0);
lean_dec(v_unused_763_);
v___x_755_ = v_val_745_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_dec(v_val_745_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_val_757_; lean_object* v___x_759_; 
v_val_757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_737_, v_buckets_747_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_val_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_size_746_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_val_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_dec_ref(v_buckets_747_);
lean_dec(v_size_746_);
lean_dec_ref(v_inst_737_);
return v_val_745_;
}
}
}
else
{
lean_object* v_size_764_; lean_object* v_buckets_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_781_; 
v_size_764_ = lean_ctor_get(v_m_738_, 0);
v_buckets_765_ = lean_ctor_get(v_m_738_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_m_738_);
if (v_isSharedCheck_781_ == 0)
{
v___x_767_ = v_m_738_;
v_isShared_768_ = v_isSharedCheck_781_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_buckets_765_);
lean_inc(v_size_764_);
lean_dec(v_m_738_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_781_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___f_769_; lean_object* v_buckets_x27_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
lean_inc_n(v_a_739_, 2);
lean_inc_ref(v_inst_736_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_769_, 0, v_inst_736_);
lean_closure_set(v___f_769_, 1, v_a_739_);
lean_closure_set(v___f_769_, 2, v_f_740_);
lean_inc_ref(v_inst_737_);
v_buckets_x27_770_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_737_, v_buckets_765_, v_a_739_, v___f_769_);
lean_inc_ref(v_buckets_x27_770_);
v___x_771_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_770_);
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_736_, v_inst_737_, v___x_771_, v_a_739_);
lean_dec_ref(v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_sub(v_size_764_, v___x_773_);
lean_dec(v_size_764_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_buckets_x27_770_);
lean_ctor_set(v___x_767_, 0, v___x_774_);
v___x_776_ = v___x_767_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_buckets_x27_770_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v___x_779_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_buckets_x27_770_);
v___x_779_ = v___x_767_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_size_764_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_buckets_x27_770_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098(lean_object* v_00_u03b1_782_, lean_object* v_00_u03b2_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_f_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(v_inst_784_, v_inst_785_, v_m_787_, v_a_788_, v_f_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0(lean_object* v_f_791_, lean_object* v_x_792_){
_start:
{
if (lean_obj_tag(v_x_792_) == 0)
{
lean_dec(v_f_791_);
return v_x_792_;
}
else
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_val_793_ = lean_ctor_get(v_x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_795_ = v_x_792_;
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v_x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_801_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_apply_1(v_f_791_, v_val_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_m_804_, lean_object* v_a_805_, lean_object* v_f_806_){
_start:
{
lean_object* v___f_807_; lean_object* v___x_808_; 
v___f_807_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_807_, 0, v_f_806_);
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(v_inst_802_, v_inst_803_, v_m_804_, v_a_805_, v___f_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098(lean_object* v_00_u03b1_809_, lean_object* v_00_u03b2_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_m_814_, lean_object* v_a_815_, lean_object* v_f_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(v_inst_811_, v_inst_812_, v_m_814_, v_a_815_, v_f_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0(lean_object* v_inst_818_, lean_object* v_a_819_, lean_object* v_f_820_, lean_object* v_l_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(v_inst_818_, v_a_819_, v_f_820_, v_l_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_f_827_){
_start:
{
uint8_t v___x_828_; 
lean_inc(v_a_826_);
lean_inc_ref(v_inst_824_);
lean_inc_ref(v_inst_823_);
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_823_, v_inst_824_, v_m_825_, v_a_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec_ref(v_inst_823_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_apply_1(v_f_827_, v___x_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_dec(v_a_826_);
lean_dec_ref(v_inst_824_);
return v_m_825_;
}
else
{
lean_object* v_val_831_; lean_object* v_val_832_; lean_object* v_size_833_; lean_object* v_buckets_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_val_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref(v___x_830_);
lean_inc_ref(v_inst_824_);
v_val_832_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_824_, v_m_825_, v_a_826_, v_val_831_);
v_size_833_ = lean_ctor_get(v_val_832_, 0);
lean_inc(v_size_833_);
v_buckets_834_ = lean_ctor_get(v_val_832_, 1);
lean_inc_ref(v_buckets_834_);
v___x_835_ = lean_unsigned_to_nat(4u);
v___x_836_ = lean_nat_mul(v_size_833_, v___x_835_);
v___x_837_ = lean_unsigned_to_nat(3u);
v___x_838_ = lean_nat_div(v___x_836_, v___x_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_array_get_size(v_buckets_834_);
v___x_840_ = lean_nat_dec_le(v___x_838_, v___x_839_);
lean_dec(v___x_838_);
if (v___x_840_ == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_isSharedCheck_848_ = !lean_is_exclusive(v_val_832_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_849_ = lean_ctor_get(v_val_832_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_val_832_, 0);
lean_dec(v_unused_850_);
v___x_842_ = v_val_832_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_val_832_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_val_844_; lean_object* v___x_846_; 
v_val_844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_824_, v_buckets_834_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_val_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_size_833_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_val_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_dec_ref(v_buckets_834_);
lean_dec(v_size_833_);
lean_dec_ref(v_inst_824_);
return v_val_832_;
}
}
}
else
{
lean_object* v_size_851_; lean_object* v_buckets_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_868_; 
v_size_851_ = lean_ctor_get(v_m_825_, 0);
v_buckets_852_ = lean_ctor_get(v_m_825_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_m_825_);
if (v_isSharedCheck_868_ == 0)
{
v___x_854_ = v_m_825_;
v_isShared_855_ = v_isSharedCheck_868_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_buckets_852_);
lean_inc(v_size_851_);
lean_dec(v_m_825_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_868_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___f_856_; lean_object* v_buckets_x27_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
lean_inc_n(v_a_826_, 2);
lean_inc_ref(v_inst_823_);
v___f_856_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_856_, 0, v_inst_823_);
lean_closure_set(v___f_856_, 1, v_a_826_);
lean_closure_set(v___f_856_, 2, v_f_827_);
lean_inc_ref(v_inst_824_);
v_buckets_x27_857_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_824_, v_buckets_852_, v_a_826_, v___f_856_);
lean_inc_ref(v_buckets_x27_857_);
v___x_858_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_857_);
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_823_, v_inst_824_, v___x_858_, v_a_826_);
lean_dec_ref(v___x_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_sub(v_size_851_, v___x_860_);
lean_dec(v_size_851_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v_buckets_x27_857_);
lean_ctor_set(v___x_854_, 0, v___x_861_);
v___x_863_ = v___x_854_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_buckets_x27_857_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_object* v___x_866_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v_buckets_x27_857_);
v___x_866_ = v___x_854_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_size_851_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_buckets_x27_857_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098(lean_object* v_00_u03b1_869_, lean_object* v_00_u03b2_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_m_873_, lean_object* v_a_874_, lean_object* v_f_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(v_inst_871_, v_inst_872_, v_m_873_, v_a_874_, v_f_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0(lean_object* v_f_877_, lean_object* v_option_878_){
_start:
{
if (lean_obj_tag(v_option_878_) == 0)
{
lean_dec(v_f_877_);
return v_option_878_;
}
else
{
lean_object* v_val_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_887_; 
v_val_879_ = lean_ctor_get(v_option_878_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_option_878_);
if (v_isSharedCheck_887_ == 0)
{
v___x_881_ = v_option_878_;
v_isShared_882_ = v_isSharedCheck_887_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_val_879_);
lean_dec(v_option_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_887_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_apply_1(v_f_877_, v_val_879_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_885_ = v___x_881_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_m_890_, lean_object* v_a_891_, lean_object* v_f_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; 
v___f_893_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_893_, 0, v_f_892_);
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(v_inst_888_, v_inst_889_, v_m_890_, v_a_891_, v___f_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_m_899_, lean_object* v_a_900_, lean_object* v_f_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(v_inst_897_, v_inst_898_, v_m_899_, v_a_900_, v_f_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(lean_object* v_f_903_, lean_object* v_acc_904_, lean_object* v_a_905_){
_start:
{
if (lean_obj_tag(v_a_905_) == 0)
{
lean_dec_ref(v_f_903_);
return v_acc_904_;
}
else
{
lean_object* v_key_906_; lean_object* v_value_907_; lean_object* v_tail_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_919_; 
v_key_906_ = lean_ctor_get(v_a_905_, 0);
v_value_907_ = lean_ctor_get(v_a_905_, 1);
v_tail_908_ = lean_ctor_get(v_a_905_, 2);
v_isSharedCheck_919_ = !lean_is_exclusive(v_a_905_);
if (v_isSharedCheck_919_ == 0)
{
v___x_910_ = v_a_905_;
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_tail_908_);
lean_inc(v_value_907_);
lean_inc(v_key_906_);
lean_dec(v_a_905_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_919_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; 
lean_inc_ref(v_f_903_);
lean_inc(v_key_906_);
v___x_912_ = lean_apply_2(v_f_903_, v_key_906_, v_value_907_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_del_object(v___x_910_);
lean_dec(v_key_906_);
v_a_905_ = v_tail_908_;
goto _start;
}
else
{
lean_object* v_val_914_; lean_object* v___x_916_; 
v_val_914_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_val_914_);
lean_dec_ref(v___x_912_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 2, v_acc_904_);
lean_ctor_set(v___x_910_, 1, v_val_914_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_key_906_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_val_914_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v_acc_904_);
v___x_916_ = v_reuseFailAlloc_918_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
v_acc_904_ = v___x_916_;
v_a_905_ = v_tail_908_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0(lean_object* v_f_920_, lean_object* v_l_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_box(0);
v___x_923_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_920_, v___x_922_, v_l_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(lean_object* v_m_924_, lean_object* v_f_925_){
_start:
{
lean_object* v_buckets_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_buckets_926_ = lean_ctor_get(v_m_924_, 1);
lean_inc_ref(v_buckets_926_);
lean_dec_ref(v_m_924_);
v___f_927_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_927_, 0, v_f_925_);
v___x_928_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_926_, v___f_927_);
v___x_929_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(lean_object* v_00_u03b1_930_, lean_object* v_00_u03b2_931_, lean_object* v_00_u03b4_932_, lean_object* v_m_933_, lean_object* v_f_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(v_m_933_, v_f_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_00_u03b4_938_, lean_object* v_f_939_, lean_object* v_acc_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_939_, v_acc_940_, v_a_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(lean_object* v_f_943_, lean_object* v_acc_944_, lean_object* v_a_945_){
_start:
{
if (lean_obj_tag(v_a_945_) == 0)
{
lean_dec(v_f_943_);
return v_acc_944_;
}
else
{
lean_object* v_key_946_; lean_object* v_value_947_; lean_object* v_tail_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_957_; 
v_key_946_ = lean_ctor_get(v_a_945_, 0);
v_value_947_ = lean_ctor_get(v_a_945_, 1);
v_tail_948_ = lean_ctor_get(v_a_945_, 2);
v_isSharedCheck_957_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_950_ = v_a_945_;
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_tail_948_);
lean_inc(v_value_947_);
lean_inc(v_key_946_);
lean_dec(v_a_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
lean_inc(v_f_943_);
lean_inc(v_key_946_);
v___x_952_ = lean_apply_2(v_f_943_, v_key_946_, v_value_947_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 2, v_acc_944_);
lean_ctor_set(v___x_950_, 1, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_key_946_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_acc_944_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_acc_944_ = v___x_954_;
v_a_945_ = v_tail_948_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0(lean_object* v_f_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_box(0);
v___x_961_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_958_, v___x_960_, v___y_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(lean_object* v_m_962_, lean_object* v_f_963_){
_start:
{
lean_object* v_size_964_; lean_object* v_buckets_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_974_; 
v_size_964_ = lean_ctor_get(v_m_962_, 0);
v_buckets_965_ = lean_ctor_get(v_m_962_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_m_962_);
if (v_isSharedCheck_974_ == 0)
{
v___x_967_ = v_m_962_;
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_buckets_965_);
lean_inc(v_size_964_);
lean_dec(v_m_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___f_969_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_969_, 0, v_f_963_);
v___x_970_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_965_, v___f_969_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_970_);
v___x_972_ = v___x_967_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_size_964_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098(lean_object* v_00_u03b1_975_, lean_object* v_00_u03b2_976_, lean_object* v_00_u03b4_977_, lean_object* v_m_978_, lean_object* v_f_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(v_m_978_, v_f_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(lean_object* v_00_u03b1_981_, lean_object* v_00_u03b2_982_, lean_object* v_00_u03b4_983_, lean_object* v_f_984_, lean_object* v_acc_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_984_, v_acc_985_, v_a_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(lean_object* v_f_988_, lean_object* v_acc_989_, lean_object* v_a_990_){
_start:
{
if (lean_obj_tag(v_a_990_) == 0)
{
lean_dec_ref(v_f_988_);
return v_acc_989_;
}
else
{
lean_object* v_key_991_; lean_object* v_value_992_; lean_object* v_tail_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1004_; 
v_key_991_ = lean_ctor_get(v_a_990_, 0);
v_value_992_ = lean_ctor_get(v_a_990_, 1);
v_tail_993_ = lean_ctor_get(v_a_990_, 2);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_990_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_995_ = v_a_990_;
v_isShared_996_ = v_isSharedCheck_1004_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_tail_993_);
lean_inc(v_value_992_);
lean_inc(v_key_991_);
lean_dec(v_a_990_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1004_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
lean_inc_ref(v_f_988_);
lean_inc(v_value_992_);
lean_inc(v_key_991_);
v___x_997_ = lean_apply_2(v_f_988_, v_key_991_, v_value_992_);
v___x_998_ = lean_unbox(v___x_997_);
if (v___x_998_ == 0)
{
lean_del_object(v___x_995_);
lean_dec(v_value_992_);
lean_dec(v_key_991_);
v_a_990_ = v_tail_993_;
goto _start;
}
else
{
lean_object* v___x_1001_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 2, v_acc_989_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_key_991_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_value_992_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_acc_989_);
v___x_1001_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
v_acc_989_ = v___x_1001_;
v_a_990_ = v_tail_993_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0(lean_object* v_f_1005_, lean_object* v_l_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_1005_, v___x_1007_, v_l_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(lean_object* v_m_1009_, lean_object* v_f_1010_){
_start:
{
lean_object* v_buckets_1011_; lean_object* v___f_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_buckets_1011_ = lean_ctor_get(v_m_1009_, 1);
lean_inc_ref(v_buckets_1011_);
lean_dec_ref(v_m_1009_);
v___f_1012_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1012_, 0, v_f_1010_);
v___x_1013_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_1011_, v___f_1012_);
v___x_1014_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(lean_object* v_00_u03b1_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_m_1017_, lean_object* v_f_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_1017_, v_f_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(lean_object* v_00_u03b1_1020_, lean_object* v_00_u03b2_1021_, lean_object* v_f_1022_, lean_object* v_acc_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_1022_, v_acc_1023_, v_a_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_m_1028_, lean_object* v_l_1029_){
_start:
{
if (lean_obj_tag(v_l_1029_) == 0)
{
lean_dec_ref(v_inst_1027_);
lean_dec_ref(v_inst_1026_);
return v_m_1028_;
}
else
{
lean_object* v_head_1030_; lean_object* v_tail_1031_; lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1034_; 
v_head_1030_ = lean_ctor_get(v_l_1029_, 0);
lean_inc(v_head_1030_);
v_tail_1031_ = lean_ctor_get(v_l_1029_, 1);
lean_inc(v_tail_1031_);
lean_dec_ref(v_l_1029_);
v_fst_1032_ = lean_ctor_get(v_head_1030_, 0);
lean_inc(v_fst_1032_);
v_snd_1033_ = lean_ctor_get(v_head_1030_, 1);
lean_inc(v_snd_1033_);
lean_dec(v_head_1030_);
lean_inc_ref(v_inst_1027_);
lean_inc_ref(v_inst_1026_);
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1026_, v_inst_1027_, v_m_1028_, v_fst_1032_, v_snd_1033_);
v_m_1028_ = v___x_1034_;
v_l_1029_ = v_tail_1031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_m_1040_, lean_object* v_l_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(v_inst_1038_, v_inst_1039_, v_m_1040_, v_l_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_m_1045_, lean_object* v_l_1046_){
_start:
{
if (lean_obj_tag(v_l_1046_) == 0)
{
lean_dec_ref(v_inst_1044_);
lean_dec_ref(v_inst_1043_);
return v_m_1045_;
}
else
{
lean_object* v_head_1047_; lean_object* v_tail_1048_; lean_object* v___x_1049_; 
v_head_1047_ = lean_ctor_get(v_l_1046_, 0);
lean_inc(v_head_1047_);
v_tail_1048_ = lean_ctor_get(v_l_1046_, 1);
lean_inc(v_tail_1048_);
lean_dec_ref(v_l_1046_);
lean_inc_ref(v_inst_1044_);
lean_inc_ref(v_inst_1043_);
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1043_, v_inst_1044_, v_m_1045_, v_head_1047_);
v_m_1045_ = v___x_1049_;
v_l_1046_ = v_tail_1048_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_m_1055_, lean_object* v_l_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(v_inst_1053_, v_inst_1054_, v_m_1055_, v_l_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_m_u2082_1060_, uint8_t v___x_1061_, lean_object* v_k_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_1058_, v_inst_1059_, v_m_u2082_1060_, v_k_1062_);
if (v___x_1064_ == 0)
{
return v___x_1061_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = 0;
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_m_u2082_1068_, lean_object* v___x_1069_, lean_object* v_k_1070_, lean_object* v_x_1071_){
_start:
{
uint8_t v___x_52__boxed_1072_; uint8_t v_res_1073_; lean_object* v_r_1074_; 
v___x_52__boxed_1072_ = lean_unbox(v___x_1069_);
v_res_1073_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(v_inst_1066_, v_inst_1067_, v_m_u2082_1068_, v___x_52__boxed_1072_, v_k_1070_, v_x_1071_);
lean_dec(v_x_1071_);
lean_dec_ref(v_m_u2082_1068_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_m_u2081_1100_, lean_object* v_m_u2082_1101_){
_start:
{
lean_object* v_size_1102_; lean_object* v_size_1103_; lean_object* v_buckets_1104_; uint8_t v___x_1105_; 
v_size_1102_ = lean_ctor_get(v_m_u2081_1100_, 0);
v_size_1103_ = lean_ctor_get(v_m_u2082_1101_, 0);
v_buckets_1104_ = lean_ctor_get(v_m_u2082_1101_, 1);
v___x_1105_ = lean_nat_dec_le(v_size_1102_, v_size_1103_);
if (v___x_1105_ == 0)
{
lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_inc_ref(v_buckets_1104_);
lean_dec_ref(v_m_u2082_1101_);
v___f_1106_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11));
v___x_1107_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1104_);
v___x_1108_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1106_, v_inst_1098_, v_inst_1099_, v_m_u2081_1100_, v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_box(v___x_1105_);
v___f_1110_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1110_, 0, v_inst_1098_);
lean_closure_set(v___f_1110_, 1, v_inst_1099_);
lean_closure_set(v___f_1110_, 2, v_m_u2082_1101_);
lean_closure_set(v___f_1110_, 3, v___x_1109_);
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_u2081_1100_, v___f_1110_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_m_u2081_1116_, lean_object* v_m_u2082_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(v_inst_1114_, v_inst_1115_, v_m_u2081_1116_, v_m_u2082_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_m_1121_, lean_object* v_l_1122_){
_start:
{
if (lean_obj_tag(v_l_1122_) == 0)
{
lean_dec_ref(v_inst_1120_);
lean_dec_ref(v_inst_1119_);
return v_m_1121_;
}
else
{
lean_object* v_head_1123_; lean_object* v_tail_1124_; lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v___x_1127_; 
v_head_1123_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_head_1123_);
v_tail_1124_ = lean_ctor_get(v_l_1122_, 1);
lean_inc(v_tail_1124_);
lean_dec_ref(v_l_1122_);
v_fst_1125_ = lean_ctor_get(v_head_1123_, 0);
lean_inc(v_fst_1125_);
v_snd_1126_ = lean_ctor_get(v_head_1123_, 1);
lean_inc(v_snd_1126_);
lean_dec(v_head_1123_);
lean_inc_ref(v_inst_1120_);
lean_inc_ref(v_inst_1119_);
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1119_, v_inst_1120_, v_m_1121_, v_fst_1125_, v_snd_1126_);
v_m_1121_ = v___x_1127_;
v_l_1122_ = v_tail_1124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_m_1133_, lean_object* v_l_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1131_, v_inst_1132_, v_m_1133_, v_l_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_m_u2081_1138_, lean_object* v_m_u2082_1139_){
_start:
{
lean_object* v_size_1140_; lean_object* v_buckets_1141_; lean_object* v_size_1142_; lean_object* v_buckets_1143_; uint8_t v___x_1144_; 
v_size_1140_ = lean_ctor_get(v_m_u2081_1138_, 0);
v_buckets_1141_ = lean_ctor_get(v_m_u2081_1138_, 1);
v_size_1142_ = lean_ctor_get(v_m_u2082_1139_, 0);
v_buckets_1143_ = lean_ctor_get(v_m_u2082_1139_, 1);
v___x_1144_ = lean_nat_dec_le(v_size_1140_, v_size_1142_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_inc_ref(v_buckets_1143_);
lean_dec_ref(v_m_u2082_1139_);
v___x_1145_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1143_);
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(v_inst_1136_, v_inst_1137_, v_m_u2081_1138_, v___x_1145_);
return v___x_1146_;
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc_ref(v_buckets_1141_);
lean_dec_ref(v_m_u2081_1138_);
v___x_1147_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1141_);
v___x_1148_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1136_, v_inst_1137_, v_m_u2082_1139_, v___x_1147_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_m_u2081_1153_, lean_object* v_m_u2082_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(v_inst_1151_, v_inst_1152_, v_m_u2081_1153_, v_m_u2082_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_m_1158_, lean_object* v_sofar_1159_, lean_object* v_k_1160_){
_start:
{
lean_object* v___x_1161_; 
lean_inc_ref(v_inst_1157_);
lean_inc_ref(v_inst_1156_);
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_1156_, v_inst_1157_, v_m_1158_, v_k_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_dec_ref(v_inst_1157_);
lean_dec_ref(v_inst_1156_);
return v_sofar_1159_;
}
else
{
lean_object* v_val_1162_; lean_object* v_fst_1163_; lean_object* v_snd_1164_; lean_object* v___x_1165_; 
v_val_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v___x_1161_);
v_fst_1163_ = lean_ctor_get(v_val_1162_, 0);
lean_inc(v_fst_1163_);
v_snd_1164_ = lean_ctor_get(v_val_1162_, 1);
lean_inc(v_snd_1164_);
lean_dec(v_val_1162_);
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(v_inst_1156_, v_inst_1157_, v_sofar_1159_, v_fst_1163_, v_snd_1164_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_m_1168_, lean_object* v_sofar_1169_, lean_object* v_k_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1166_, v_inst_1167_, v_m_1168_, v_sofar_1169_, v_k_1170_);
lean_dec_ref(v_m_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_m_1176_, lean_object* v_sofar_1177_, lean_object* v_k_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1174_, v_inst_1175_, v_m_1176_, v_sofar_1177_, v_k_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_00_u03b2_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_m_1184_, lean_object* v_sofar_1185_, lean_object* v_k_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(v_00_u03b1_1180_, v_00_u03b2_1181_, v_inst_1182_, v_inst_1183_, v_m_1184_, v_sofar_1185_, v_k_1186_);
lean_dec_ref(v_m_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_m_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_buckets_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_buckets_1192_ = lean_ctor_get(v_m_1190_, 1);
lean_inc(v_a_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1189_, v_buckets_1192_, v_a_1191_);
v___x_1194_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1188_, v_a_1191_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_m_1197_, lean_object* v_a_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1195_, v_inst_1196_, v_m_1197_, v_a_1198_);
lean_dec_ref(v_m_1197_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_m_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1202_, v_inst_1203_, v_m_1204_, v_a_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(lean_object* v_00_u03b1_1207_, lean_object* v_00_u03b2_1208_, lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_m_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(v_00_u03b1_1207_, v_00_u03b2_1208_, v_inst_1209_, v_inst_1210_, v_m_1211_, v_a_1212_);
lean_dec_ref(v_m_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_m_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_buckets_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_buckets_1218_ = lean_ctor_get(v_m_1216_, 1);
lean_inc(v_a_1217_);
v___x_1219_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1215_, v_buckets_1218_, v_a_1217_);
v___x_1220_ = l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1214_, v_a_1217_, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_1221_, v_inst_1222_, v_m_1223_, v_a_1224_);
lean_dec_ref(v_m_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(lean_object* v_00_u03b1_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_, lean_object* v_h_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_1228_, v_inst_1229_, v_m_1230_, v_a_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_h_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(v_00_u03b1_1234_, v_00_u03b2_1235_, v_inst_1236_, v_inst_1237_, v_m_1238_, v_a_1239_, v_h_1240_);
lean_dec_ref(v_m_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_, lean_object* v_fallback_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1242_, v_inst_1243_, v_m_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_inc(v_fallback_1246_);
return v_fallback_1246_;
}
else
{
lean_object* v_val_1248_; 
v_val_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1248_);
lean_dec_ref(v___x_1247_);
return v_val_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_fallback_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_1249_, v_inst_1250_, v_m_1251_, v_a_1252_, v_fallback_1253_);
lean_dec(v_fallback_1253_);
lean_dec_ref(v_m_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(lean_object* v_00_u03b1_1255_, lean_object* v_00_u03b2_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_m_1259_, lean_object* v_a_1260_, lean_object* v_fallback_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_1257_, v_inst_1258_, v_m_1259_, v_a_1260_, v_fallback_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_00_u03b2_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_m_1267_, lean_object* v_a_1268_, lean_object* v_fallback_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(v_00_u03b1_1263_, v_00_u03b2_1264_, v_inst_1265_, v_inst_1266_, v_m_1267_, v_a_1268_, v_fallback_1269_);
lean_dec(v_fallback_1269_);
lean_dec_ref(v_m_1267_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_m_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1271_, v_inst_1272_, v_m_1274_, v_a_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_1278_ = l_panic___redArg(v_inst_1273_, v___x_1277_);
return v___x_1278_;
}
else
{
lean_object* v_val_1279_; 
v_val_1279_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_val_1279_);
lean_dec_ref(v___x_1276_);
return v_val_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_m_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_1280_, v_inst_1281_, v_inst_1282_, v_m_1283_, v_a_1284_);
lean_dec_ref(v_m_1283_);
lean_dec(v_inst_1282_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(lean_object* v_00_u03b1_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_m_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_1288_, v_inst_1289_, v_inst_1290_, v_m_1291_, v_a_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_00_u03b2_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_m_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(v_00_u03b1_1294_, v_00_u03b2_1295_, v_inst_1296_, v_inst_1297_, v_inst_1298_, v_m_1299_, v_a_1300_);
lean_dec_ref(v_m_1299_);
lean_dec(v_inst_1298_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_m_1304_, lean_object* v_l_1305_){
_start:
{
if (lean_obj_tag(v_l_1305_) == 0)
{
lean_dec_ref(v_inst_1303_);
lean_dec_ref(v_inst_1302_);
return v_m_1304_;
}
else
{
lean_object* v_head_1306_; lean_object* v_tail_1307_; lean_object* v_fst_1308_; lean_object* v_snd_1309_; lean_object* v___x_1310_; 
v_head_1306_ = lean_ctor_get(v_l_1305_, 0);
lean_inc(v_head_1306_);
v_tail_1307_ = lean_ctor_get(v_l_1305_, 1);
lean_inc(v_tail_1307_);
lean_dec_ref(v_l_1305_);
v_fst_1308_ = lean_ctor_get(v_head_1306_, 0);
lean_inc(v_fst_1308_);
v_snd_1309_ = lean_ctor_get(v_head_1306_, 1);
lean_inc(v_snd_1309_);
lean_dec(v_head_1306_);
lean_inc_ref(v_inst_1303_);
lean_inc_ref(v_inst_1302_);
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1302_, v_inst_1303_, v_m_1304_, v_fst_1308_, v_snd_1309_);
v_m_1304_ = v___x_1310_;
v_l_1305_ = v_tail_1307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(lean_object* v_00_u03b1_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_m_1316_, lean_object* v_l_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(v_inst_1314_, v_inst_1315_, v_m_1316_, v_l_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_m_1321_, lean_object* v_l_1322_){
_start:
{
if (lean_obj_tag(v_l_1322_) == 0)
{
lean_dec_ref(v_inst_1320_);
lean_dec_ref(v_inst_1319_);
return v_m_1321_;
}
else
{
lean_object* v_head_1323_; lean_object* v_tail_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v_head_1323_ = lean_ctor_get(v_l_1322_, 0);
lean_inc(v_head_1323_);
v_tail_1324_ = lean_ctor_get(v_l_1322_, 1);
lean_inc(v_tail_1324_);
lean_dec_ref(v_l_1322_);
v___x_1325_ = lean_box(0);
lean_inc_ref(v_inst_1320_);
lean_inc_ref(v_inst_1319_);
v___x_1326_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1319_, v_inst_1320_, v_m_1321_, v_head_1323_, v___x_1325_);
v_m_1321_ = v___x_1326_;
v_l_1322_ = v_tail_1324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(lean_object* v_00_u03b1_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_m_1331_, lean_object* v_l_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(v_inst_1329_, v_inst_1330_, v_m_1331_, v_l_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object* v_m_1334_, lean_object* v_h__1_1335_){
_start:
{
lean_object* v_size_1336_; lean_object* v_buckets_1337_; lean_object* v___x_1338_; 
v_size_1336_ = lean_ctor_get(v_m_1334_, 0);
lean_inc(v_size_1336_);
v_buckets_1337_ = lean_ctor_get(v_m_1334_, 1);
lean_inc_ref(v_buckets_1337_);
lean_dec_ref(v_m_1334_);
v___x_1338_ = lean_apply_3(v_h__1_1335_, v_size_1336_, v_buckets_1337_, lean_box(0));
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object* v_00_u03b1_1339_, lean_object* v_00_u03b2_1340_, lean_object* v_motive_1341_, lean_object* v_m_1342_, lean_object* v_h__1_1343_){
_start:
{
lean_object* v_size_1344_; lean_object* v_buckets_1345_; lean_object* v___x_1346_; 
v_size_1344_ = lean_ctor_get(v_m_1342_, 0);
lean_inc(v_size_1344_);
v_buckets_1345_ = lean_ctor_get(v_m_1342_, 1);
lean_inc_ref(v_buckets_1345_);
lean_dec_ref(v_m_1342_);
v___x_1346_ = lean_apply_3(v_h__1_1343_, v_size_1344_, v_buckets_1345_, lean_box(0));
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___redArg(lean_object* v_x_1347_, lean_object* v_h__1_1348_, lean_object* v_h__2_1349_){
_start:
{
if (lean_obj_tag(v_x_1347_) == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_h__2_1349_);
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_apply_1(v_h__1_1348_, v___x_1350_);
return v___x_1351_;
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1353_; 
lean_dec(v_h__1_1348_);
v_val_1352_ = lean_ctor_get(v_x_1347_, 0);
lean_inc(v_val_1352_);
lean_dec_ref(v_x_1347_);
v___x_1353_ = lean_apply_1(v_h__2_1349_, v_val_1352_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_a_1356_, lean_object* v_motive_1357_, lean_object* v_x_1358_, lean_object* v_h__1_1359_, lean_object* v_h__2_1360_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_h__2_1360_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_apply_1(v_h__1_1359_, v___x_1361_);
return v___x_1362_;
}
else
{
lean_object* v_val_1363_; lean_object* v___x_1364_; 
lean_dec(v_h__1_1359_);
v_val_1363_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_val_1363_);
lean_dec_ref(v_x_1358_);
v___x_1364_ = lean_apply_1(v_h__2_1360_, v_val_1363_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_a_1367_, lean_object* v_motive_1368_, lean_object* v_x_1369_, lean_object* v_h__1_1370_, lean_object* v_h__2_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(v_00_u03b1_1365_, v_00_u03b2_1366_, v_a_1367_, v_motive_1368_, v_x_1369_, v_h__1_1370_, v_h__2_1371_);
lean_dec(v_a_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_1373_, lean_object* v_h__1_1374_, lean_object* v_h__2_1375_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_h__2_1375_);
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_apply_1(v_h__1_1374_, v___x_1376_);
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; lean_object* v___x_1379_; 
lean_dec(v_h__1_1374_);
v_val_1378_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_val_1378_);
lean_dec_ref(v_x_1373_);
v___x_1379_ = lean_apply_1(v_h__2_1375_, v_val_1378_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_a_1382_, lean_object* v_motive_1383_, lean_object* v_x_1384_, lean_object* v_h__1_1385_, lean_object* v_h__2_1386_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__2_1386_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_apply_1(v_h__1_1385_, v___x_1387_);
return v___x_1388_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__1_1385_);
v_val_1389_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_val_1389_);
lean_dec_ref(v_x_1384_);
v___x_1390_ = lean_apply_1(v_h__2_1386_, v_val_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_00_u03b2_1392_, lean_object* v_a_1393_, lean_object* v_motive_1394_, lean_object* v_x_1395_, lean_object* v_h__1_1396_, lean_object* v_h__2_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_1391_, v_00_u03b2_1392_, v_a_1393_, v_motive_1394_, v_x_1395_, v_h__1_1396_, v_h__2_1397_);
lean_dec(v_a_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(size_t v_x_1399_, lean_object* v_h__1_1400_){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_box_usize(v_x_1399_);
v___x_1402_ = lean_apply_2(v_h__1_1400_, v___x_1401_, lean_box(0));
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg___boxed(lean_object* v_x_1403_, lean_object* v_h__1_1404_){
_start:
{
size_t v_x_14__boxed_1405_; lean_object* v_res_1406_; 
v_x_14__boxed_1405_ = lean_unbox_usize(v_x_1403_);
lean_dec(v_x_1403_);
v_res_1406_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(v_x_14__boxed_1405_, v_h__1_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(lean_object* v_00_u03b1_1407_, lean_object* v_00_u03b2_1408_, lean_object* v_data_1409_, lean_object* v_motive_1410_, size_t v_x_1411_, lean_object* v_h__1_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_box_usize(v_x_1411_);
v___x_1414_ = lean_apply_2(v_h__1_1412_, v___x_1413_, lean_box(0));
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_data_1417_, lean_object* v_motive_1418_, lean_object* v_x_1419_, lean_object* v_h__1_1420_){
_start:
{
size_t v_x_21__boxed_1421_; lean_object* v_res_1422_; 
v_x_21__boxed_1421_ = lean_unbox_usize(v_x_1419_);
lean_dec(v_x_1419_);
v_res_1422_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(v_00_u03b1_1415_, v_00_u03b2_1416_, v_data_1417_, v_motive_1418_, v_x_21__boxed_1421_, v_h__1_1420_);
lean_dec_ref(v_data_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter___redArg(lean_object* v_m_1423_, lean_object* v_h__1_1424_){
_start:
{
lean_object* v_size_1425_; lean_object* v_buckets_1426_; lean_object* v___x_1427_; 
v_size_1425_ = lean_ctor_get(v_m_1423_, 0);
lean_inc(v_size_1425_);
v_buckets_1426_ = lean_ctor_get(v_m_1423_, 1);
lean_inc_ref(v_buckets_1426_);
lean_dec_ref(v_m_1423_);
v___x_1427_ = lean_apply_3(v_h__1_1424_, v_size_1425_, v_buckets_1426_, lean_box(0));
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_motive_1430_, lean_object* v_m_1431_, lean_object* v_h__1_1432_){
_start:
{
lean_object* v_size_1433_; lean_object* v_buckets_1434_; lean_object* v___x_1435_; 
v_size_1433_ = lean_ctor_get(v_m_1431_, 0);
lean_inc(v_size_1433_);
v_buckets_1434_ = lean_ctor_get(v_m_1431_, 1);
lean_inc_ref(v_buckets_1434_);
lean_dec_ref(v_m_1431_);
v___x_1435_ = lean_apply_3(v_h__1_1432_, v_size_1433_, v_buckets_1434_, lean_box(0));
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(lean_object* v_x_1436_, lean_object* v_h__1_1437_, lean_object* v_h__2_1438_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec(v_h__2_1438_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_apply_1(v_h__1_1437_, v___x_1439_);
return v___x_1440_;
}
else
{
lean_object* v_val_1441_; lean_object* v___x_1442_; 
lean_dec(v_h__1_1437_);
v_val_1441_ = lean_ctor_get(v_x_1436_, 0);
lean_inc(v_val_1441_);
lean_dec_ref(v_x_1436_);
v___x_1442_ = lean_apply_1(v_h__2_1438_, v_val_1441_);
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(lean_object* v_00_u03b2_1443_, lean_object* v_motive_1444_, lean_object* v_x_1445_, lean_object* v_h__1_1446_, lean_object* v_h__2_1447_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec(v_h__2_1447_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_apply_1(v_h__1_1446_, v___x_1448_);
return v___x_1449_;
}
else
{
lean_object* v_val_1450_; lean_object* v___x_1451_; 
lean_dec(v_h__1_1446_);
v_val_1450_ = lean_ctor_get(v_x_1445_, 0);
lean_inc(v_val_1450_);
lean_dec_ref(v_x_1445_);
v___x_1451_ = lean_apply_1(v_h__2_1447_, v_val_1450_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_1452_, lean_object* v_h__1_1453_, lean_object* v_h__2_1454_){
_start:
{
if (lean_obj_tag(v_x_1452_) == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_h__2_1454_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_apply_1(v_h__1_1453_, v___x_1455_);
return v___x_1456_;
}
else
{
lean_object* v_val_1457_; lean_object* v___x_1458_; 
lean_dec(v_h__1_1453_);
v_val_1457_ = lean_ctor_get(v_x_1452_, 0);
lean_inc(v_val_1457_);
lean_dec_ref(v_x_1452_);
v___x_1458_ = lean_apply_1(v_h__2_1454_, v_val_1457_);
return v___x_1458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_1459_, lean_object* v_motive_1460_, lean_object* v_x_1461_, lean_object* v_h__1_1462_, lean_object* v_h__2_1463_){
_start:
{
if (lean_obj_tag(v_x_1461_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_dec(v_h__2_1463_);
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_apply_1(v_h__1_1462_, v___x_1464_);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1467_; 
lean_dec(v_h__1_1462_);
v_val_1466_ = lean_ctor_get(v_x_1461_, 0);
lean_inc(v_val_1466_);
lean_dec_ref(v_x_1461_);
v___x_1467_ = lean_apply_1(v_h__2_1463_, v_val_1466_);
return v___x_1467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(size_t v_x_1468_, lean_object* v_h__1_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_box_usize(v_x_1468_);
v___x_1471_ = lean_apply_2(v_h__1_1469_, v___x_1470_, lean_box(0));
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(lean_object* v_x_1472_, lean_object* v_h__1_1473_){
_start:
{
size_t v_x_14__boxed_1474_; lean_object* v_res_1475_; 
v_x_14__boxed_1474_ = lean_unbox_usize(v_x_1472_);
lean_dec(v_x_1472_);
v_res_1475_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(v_x_14__boxed_1474_, v_h__1_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object* v_00_u03b1_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_buckets_1478_, lean_object* v_motive_1479_, size_t v_x_1480_, lean_object* v_h__1_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_box_usize(v_x_1480_);
v___x_1483_ = lean_apply_2(v_h__1_1481_, v___x_1482_, lean_box(0));
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(lean_object* v_00_u03b1_1484_, lean_object* v_00_u03b2_1485_, lean_object* v_buckets_1486_, lean_object* v_motive_1487_, lean_object* v_x_1488_, lean_object* v_h__1_1489_){
_start:
{
size_t v_x_21__boxed_1490_; lean_object* v_res_1491_; 
v_x_21__boxed_1490_ = lean_unbox_usize(v_x_1488_);
lean_dec(v_x_1488_);
v_res_1491_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(v_00_u03b1_1484_, v_00_u03b2_1485_, v_buckets_1486_, v_motive_1487_, v_x_21__boxed_1490_, v_h__1_1489_);
lean_dec_ref(v_buckets_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(lean_object* v_l_1492_, lean_object* v_h__1_1493_, lean_object* v_h__2_1494_){
_start:
{
if (lean_obj_tag(v_l_1492_) == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v_h__2_1494_);
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_apply_1(v_h__1_1493_, v___x_1495_);
return v___x_1496_;
}
else
{
lean_object* v_head_1497_; lean_object* v_tail_1498_; lean_object* v___x_1499_; 
lean_dec(v_h__1_1493_);
v_head_1497_ = lean_ctor_get(v_l_1492_, 0);
lean_inc(v_head_1497_);
v_tail_1498_ = lean_ctor_get(v_l_1492_, 1);
lean_inc(v_tail_1498_);
lean_dec_ref(v_l_1492_);
v___x_1499_ = lean_apply_2(v_h__2_1494_, v_head_1497_, v_tail_1498_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_motive_1502_, lean_object* v_l_1503_, lean_object* v_h__1_1504_, lean_object* v_h__2_1505_){
_start:
{
if (lean_obj_tag(v_l_1503_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_h__2_1505_);
v___x_1506_ = lean_box(0);
v___x_1507_ = lean_apply_1(v_h__1_1504_, v___x_1506_);
return v___x_1507_;
}
else
{
lean_object* v_head_1508_; lean_object* v_tail_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__1_1504_);
v_head_1508_ = lean_ctor_get(v_l_1503_, 0);
lean_inc(v_head_1508_);
v_tail_1509_ = lean_ctor_get(v_l_1503_, 1);
lean_inc(v_tail_1509_);
lean_dec_ref(v_l_1503_);
v___x_1510_ = lean_apply_2(v_h__2_1505_, v_head_1508_, v_tail_1509_);
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(lean_object* v_l_1511_, lean_object* v_h__1_1512_, lean_object* v_h__2_1513_){
_start:
{
if (lean_obj_tag(v_l_1511_) == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec(v_h__2_1513_);
v___x_1514_ = lean_box(0);
v___x_1515_ = lean_apply_1(v_h__1_1512_, v___x_1514_);
return v___x_1515_;
}
else
{
lean_object* v_head_1516_; lean_object* v_tail_1517_; lean_object* v___x_1518_; 
lean_dec(v_h__1_1512_);
v_head_1516_ = lean_ctor_get(v_l_1511_, 0);
lean_inc(v_head_1516_);
v_tail_1517_ = lean_ctor_get(v_l_1511_, 1);
lean_inc(v_tail_1517_);
lean_dec_ref(v_l_1511_);
v___x_1518_ = lean_apply_2(v_h__2_1513_, v_head_1516_, v_tail_1517_);
return v___x_1518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(lean_object* v_00_u03b1_1519_, lean_object* v_motive_1520_, lean_object* v_l_1521_, lean_object* v_h__1_1522_, lean_object* v_h__2_1523_){
_start:
{
if (lean_obj_tag(v_l_1521_) == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_h__2_1523_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_apply_1(v_h__1_1522_, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v_head_1526_; lean_object* v_tail_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__1_1522_);
v_head_1526_ = lean_ctor_get(v_l_1521_, 0);
lean_inc(v_head_1526_);
v_tail_1527_ = lean_ctor_get(v_l_1521_, 1);
lean_inc(v_tail_1527_);
lean_dec_ref(v_l_1521_);
v___x_1528_ = lean_apply_2(v_h__2_1523_, v_head_1526_, v_tail_1527_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(lean_object* v_l_1529_, lean_object* v_h__1_1530_, lean_object* v_h__2_1531_){
_start:
{
if (lean_obj_tag(v_l_1529_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_h__2_1531_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_apply_1(v_h__1_1530_, v___x_1532_);
return v___x_1533_;
}
else
{
lean_object* v_head_1534_; lean_object* v_tail_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__1_1530_);
v_head_1534_ = lean_ctor_get(v_l_1529_, 0);
lean_inc(v_head_1534_);
v_tail_1535_ = lean_ctor_get(v_l_1529_, 1);
lean_inc(v_tail_1535_);
lean_dec_ref(v_l_1529_);
v___x_1536_ = lean_apply_2(v_h__2_1531_, v_head_1534_, v_tail_1535_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_motive_1539_, lean_object* v_l_1540_, lean_object* v_h__1_1541_, lean_object* v_h__2_1542_){
_start:
{
if (lean_obj_tag(v_l_1540_) == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec(v_h__2_1542_);
v___x_1543_ = lean_box(0);
v___x_1544_ = lean_apply_1(v_h__1_1541_, v___x_1543_);
return v___x_1544_;
}
else
{
lean_object* v_head_1545_; lean_object* v_tail_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__1_1541_);
v_head_1545_ = lean_ctor_get(v_l_1540_, 0);
lean_inc(v_head_1545_);
v_tail_1546_ = lean_ctor_get(v_l_1540_, 1);
lean_inc(v_tail_1546_);
lean_dec_ref(v_l_1540_);
v___x_1547_ = lean_apply_2(v_h__2_1542_, v_head_1545_, v_tail_1546_);
return v___x_1547_;
}
}
}
lean_object* runtime_initialize_Init_Data_Array_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_TakeDrop(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_HashesTo(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_HashesTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Internal_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Internal_Model(builtin);
}
#ifdef __cplusplus
}
#endif
