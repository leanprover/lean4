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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(lean_object* v_f_68_, size_t v_sz_69_, size_t v_i_70_, lean_object* v_bs_71_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_68_ = stack[0].m_obj;
size_t v_sz_69_ = stack[1].m_num;
size_t v_i_70_ = stack[2].m_num;
lean_object* v_bs_71_ = stack[3].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_68_, v_sz_69_, v_i_70_, v_bs_71_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg___boxed(lean_object* v_f_82_, lean_object* v_sz_83_, lean_object* v_i_84_, lean_object* v_bs_85_){
_start:
{
size_t v_sz_boxed_86_; size_t v_i_boxed_87_; lean_object* v_res_88_; 
v_sz_boxed_86_ = lean_unbox_usize(v_sz_83_);
lean_dec(v_sz_83_);
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_82_, v_sz_boxed_86_, v_i_boxed_87_, v_bs_85_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateAllBuckets___redArg(lean_object* v_self_89_, lean_object* v_f_90_){
_start:
{
size_t v_sz_91_; size_t v___x_92_; lean_object* v___x_93_; 
v_sz_91_ = lean_array_size(v_self_89_);
v___x_92_ = ((size_t)0ULL);
v___x_93_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_90_, v_sz_91_, v___x_92_, v_self_89_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_updateAllBuckets(lean_object* v_00_u03b1_94_, lean_object* v_00_u03b2_95_, lean_object* v_00_u03b4_96_, lean_object* v_self_97_, lean_object* v_f_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_self_97_, v_f_98_);
return v___x_99_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_00_u03b4_102_, lean_object* v_f_103_, size_t v_sz_104_, size_t v_i_105_, lean_object* v_bs_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___redArg(v_f_103_, v_sz_104_, v_i_105_, v_bs_106_);
return v___x_107_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_103_ = stack[3].m_obj;
size_t v_sz_104_ = stack[4].m_num;
size_t v_i_105_ = stack[5].m_num;
lean_object* v_bs_106_ = stack[6].m_obj;
lean_object* v_res_108_;
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(lean_box(0), lean_box(0), lean_box(0), v_f_103_, v_sz_104_, v_i_105_, v_bs_106_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0___boxed(lean_object* v_00_u03b1_109_, lean_object* v_00_u03b2_110_, lean_object* v_00_u03b4_111_, lean_object* v_f_112_, lean_object* v_sz_113_, lean_object* v_i_114_, lean_object* v_bs_115_){
_start:
{
size_t v_sz_boxed_116_; size_t v_i_boxed_117_; lean_object* v_res_118_; 
v_sz_boxed_116_ = lean_unbox_usize(v_sz_113_);
lean_dec(v_sz_113_);
v_i_boxed_117_ = lean_unbox_usize(v_i_114_);
lean_dec(v_i_114_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_updateAllBuckets_spec__0(v_00_u03b1_109_, v_00_u03b2_110_, v_00_u03b4_111_, v_f_112_, v_sz_boxed_116_, v_i_boxed_117_, v_bs_115_);
return v_res_118_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(lean_object* v_as_119_, size_t v_i_120_, size_t v_stop_121_, lean_object* v_b_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = lean_usize_dec_eq(v_i_120_, v_stop_121_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; size_t v___x_127_; size_t v___x_128_; 
v___x_124_ = lean_array_uget_borrowed(v_as_119_, v_i_120_);
v___x_125_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_124_);
v___x_126_ = lean_nat_add(v_b_122_, v___x_125_);
lean_dec(v___x_125_);
lean_dec(v_b_122_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_i_120_, v___x_127_);
v_i_120_ = v___x_128_;
v_b_122_ = v___x_126_;
goto _start;
}
else
{
return v_b_122_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_119_ = stack[0].m_obj;
size_t v_i_120_ = stack[1].m_num;
size_t v_stop_121_ = stack[2].m_num;
lean_object* v_b_122_ = stack[3].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_119_, v_i_120_, v_stop_121_, v_b_122_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg___boxed(lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_stop_133_, lean_object* v_b_134_){
_start:
{
size_t v_i_boxed_135_; size_t v_stop_boxed_136_; lean_object* v_res_137_; 
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_stop_boxed_136_ = lean_unbox_usize(v_stop_133_);
lean_dec(v_stop_133_);
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_131_, v_i_boxed_135_, v_stop_boxed_136_, v_b_134_);
lean_dec_ref(v_as_131_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize___redArg(lean_object* v_self_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_array_get_size(v_self_138_);
v___x_141_ = lean_nat_dec_lt(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_139_);
lean_ctor_set(v___x_142_, 1, v_self_138_);
return v___x_142_;
}
else
{
size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = ((size_t)0ULL);
v___x_144_ = lean_usize_of_nat(v___x_140_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_138_, v___x_143_, v___x_144_, v___x_139_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_self_138_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_self_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_self_149_);
return v___x_150_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(lean_object* v_00_u03b1_151_, lean_object* v_00_u03b2_152_, lean_object* v_as_153_, size_t v_i_154_, size_t v_stop_155_, lean_object* v_b_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_153_, v_i_154_, v_stop_155_, v_b_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_153_ = stack[2].m_obj;
size_t v_i_154_ = stack[3].m_num;
size_t v_stop_155_ = stack[4].m_num;
lean_object* v_b_156_ = stack[5].m_obj;
lean_object* v_res_158_;
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(lean_box(0), lean_box(0), v_as_153_, v_i_154_, v_stop_155_, v_b_156_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___boxed(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_as_161_, lean_object* v_i_162_, lean_object* v_stop_163_, lean_object* v_b_164_){
_start:
{
size_t v_i_boxed_165_; size_t v_stop_boxed_166_; lean_object* v_res_167_; 
v_i_boxed_165_ = lean_unbox_usize(v_i_162_);
lean_dec(v_i_162_);
v_stop_boxed_166_ = lean_unbox_usize(v_stop_163_);
lean_dec(v_stop_163_);
v_res_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(v_00_u03b1_159_, v_00_u03b2_160_, v_as_161_, v_i_boxed_165_, v_stop_boxed_166_, v_b_164_);
lean_dec_ref(v_as_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0(lean_object* v_inst_168_, lean_object* v_a_169_, lean_object* v_b_170_, lean_object* v_l_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_168_, v_a_169_, v_b_170_, v_l_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_m_175_, lean_object* v_a_176_, lean_object* v_b_177_){
_start:
{
lean_object* v_size_178_; lean_object* v_buckets_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_188_; 
v_size_178_ = lean_ctor_get(v_m_175_, 0);
v_buckets_179_ = lean_ctor_get(v_m_175_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_m_175_);
if (v_isSharedCheck_188_ == 0)
{
v___x_181_ = v_m_175_;
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_buckets_179_);
lean_inc(v_size_178_);
lean_dec(v_m_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_inc(v_a_176_);
v___f_183_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_183_, 0, v_inst_173_);
lean_closure_set(v___f_183_, 1, v_a_176_);
lean_closure_set(v___f_183_, 2, v_b_177_);
v___x_184_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_174_, v_buckets_179_, v_a_176_, v___f_183_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_size_178_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_m_193_, lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(v_inst_191_, v_inst_192_, v_m_193_, v_a_194_, v_b_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0(lean_object* v_a_197_, lean_object* v_b_198_, lean_object* v_l_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_200_, 0, v_a_197_);
lean_ctor_set(v___x_200_, 1, v_b_198_);
lean_ctor_set(v___x_200_, 2, v_l_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(lean_object* v_inst_201_, lean_object* v_m_202_, lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
lean_object* v_size_205_; lean_object* v_buckets_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_217_; 
v_size_205_ = lean_ctor_get(v_m_202_, 0);
v_buckets_206_ = lean_ctor_get(v_m_202_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_m_202_);
if (v_isSharedCheck_217_ == 0)
{
v___x_208_ = v_m_202_;
v_isShared_209_ = v_isSharedCheck_217_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_buckets_206_);
lean_inc(v_size_205_);
lean_dec(v_m_202_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_217_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___f_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
lean_inc(v_a_203_);
v___f_210_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0), 3, 2);
lean_closure_set(v___f_210_, 0, v_a_203_);
lean_closure_set(v___f_210_, 1, v_b_204_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_size_205_, v___x_211_);
lean_dec(v_size_205_);
v___x_213_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_201_, v_buckets_206_, v_a_203_, v___f_210_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_213_);
lean_ctor_set(v___x_208_, 0, v___x_212_);
v___x_215_ = v___x_208_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_m_222_, lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_221_, v_m_222_, v_a_223_, v_b_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___boxed(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_m_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(v_00_u03b1_226_, v_00_u03b2_227_, v_inst_228_, v_inst_229_, v_m_230_, v_a_231_, v_b_232_);
lean_dec_ref(v_inst_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_m_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_buckets_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_buckets_238_ = lean_ctor_get(v_m_236_, 1);
lean_inc(v_a_237_);
v___x_239_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_235_, v_buckets_238_, v_a_237_);
v___x_240_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_234_, v_a_237_, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_m_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_241_, v_inst_242_, v_m_243_, v_a_244_);
lean_dec_ref(v_m_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_m_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_248_, v_inst_250_, v_m_251_, v_a_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(lean_object* v_00_u03b1_254_, lean_object* v_00_u03b2_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_m_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(v_00_u03b1_254_, v_00_u03b2_255_, v_inst_256_, v_inst_257_, v_inst_258_, v_m_259_, v_a_260_);
lean_dec_ref(v_m_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_m_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_buckets_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_buckets_266_ = lean_ctor_get(v_m_264_, 1);
lean_inc(v_a_265_);
v___x_267_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_263_, v_buckets_266_, v_a_265_);
v___x_268_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_262_, v_a_265_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_269_, v_inst_270_, v_m_271_, v_a_272_);
lean_dec_ref(v_m_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_m_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_276_, v_inst_277_, v_m_278_, v_a_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(lean_object* v_00_u03b1_281_, lean_object* v_00_u03b2_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_m_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(v_00_u03b1_281_, v_00_u03b2_282_, v_inst_283_, v_inst_284_, v_m_285_, v_a_286_);
lean_dec_ref(v_m_285_);
return v_res_287_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_m_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_buckets_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_buckets_292_ = lean_ctor_get(v_m_290_, 1);
lean_inc(v_a_291_);
v___x_293_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_289_, v_buckets_292_, v_a_291_);
v___x_294_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_288_, v_a_291_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_288_ = stack[0].m_obj;
lean_object* v_inst_289_ = stack[1].m_obj;
lean_object* v_m_290_ = stack[2].m_obj;
lean_object* v_a_291_ = stack[3].m_obj;
uint8_t v_res_295_;
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_288_, v_inst_289_, v_m_290_, v_a_291_);
stack->m_num = v_res_295_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_296_, v_inst_297_, v_m_298_, v_a_299_);
lean_dec_ref(v_m_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_object* v_00_u03b1_302_, lean_object* v_00_u03b2_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_m_306_, lean_object* v_a_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_304_, v_inst_305_, v_m_306_, v_a_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains_u2098_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_304_ = stack[2].m_obj;
lean_object* v_inst_305_ = stack[3].m_obj;
lean_object* v_m_306_ = stack[4].m_obj;
lean_object* v_a_307_ = stack[5].m_obj;
uint8_t v_res_309_;
v_res_309_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_box(0), lean_box(0), v_inst_304_, v_inst_305_, v_m_306_, v_a_307_);
stack->m_num = v_res_309_;
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
lean_dec_ref_known(v___x_467_, 1);
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
lean_dec_ref_known(v___x_507_, 1);
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
lean_dec_ref_known(v___x_568_, 1);
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
lean_dec_ref_known(v___x_597_, 1);
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
v_buckets_631_ = lean_ctor_get(v_val_629_, 1);
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
lean_inc_ref(v_buckets_631_);
lean_inc(v_size_630_);
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
v_buckets_665_ = lean_ctor_get(v_val_663_, 1);
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
lean_inc_ref(v_buckets_665_);
lean_inc(v_size_664_);
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
lean_dec_ref_known(v___x_743_, 1);
lean_inc_ref(v_inst_737_);
v_val_745_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_737_, v_m_738_, v_a_739_, v_val_744_);
v_size_746_ = lean_ctor_get(v_val_745_, 0);
v_buckets_747_ = lean_ctor_get(v_val_745_, 1);
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
lean_inc_ref(v_buckets_747_);
lean_inc(v_size_746_);
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
lean_dec_ref_known(v___x_830_, 1);
lean_inc_ref(v_inst_824_);
v_val_832_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_824_, v_m_825_, v_a_826_, v_val_831_);
v_size_833_ = lean_ctor_get(v_val_832_, 0);
v_buckets_834_ = lean_ctor_get(v_val_832_, 1);
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
lean_inc_ref(v_buckets_834_);
lean_inc(v_size_833_);
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
lean_dec_ref_known(v___x_912_, 1);
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
lean_dec_ref_known(v_l_1029_, 2);
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
lean_dec_ref_known(v_l_1046_, 2);
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_m_u2082_1060_, uint8_t v___x_1061_, lean_object* v_k_1062_, lean_object* v_x_1063_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1058_ = stack[0].m_obj;
lean_object* v_inst_1059_ = stack[1].m_obj;
lean_object* v_m_u2082_1060_ = stack[2].m_obj;
uint8_t v___x_1061_ = stack[3].m_num;
lean_object* v_k_1062_ = stack[4].m_obj;
lean_object* v_x_1063_ = stack[5].m_obj;
uint8_t v_res_1066_;
v_res_1066_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(v_inst_1058_, v_inst_1059_, v_m_u2082_1060_, v___x_1061_, v_k_1062_, v_x_1063_);
stack->m_num = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_m_u2082_1069_, lean_object* v___x_1070_, lean_object* v_k_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v___x_55__boxed_1073_; uint8_t v_res_1074_; lean_object* v_r_1075_; 
v___x_55__boxed_1073_ = lean_unbox(v___x_1070_);
v_res_1074_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(v_inst_1067_, v_inst_1068_, v_m_u2082_1069_, v___x_55__boxed_1073_, v_k_1071_, v_x_1072_);
lean_dec(v_x_1072_);
lean_dec_ref(v_m_u2082_1069_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_m_u2081_1101_, lean_object* v_m_u2082_1102_){
_start:
{
lean_object* v_size_1103_; lean_object* v_size_1104_; lean_object* v_buckets_1105_; uint8_t v___x_1106_; 
v_size_1103_ = lean_ctor_get(v_m_u2081_1101_, 0);
v_size_1104_ = lean_ctor_get(v_m_u2082_1102_, 0);
v_buckets_1105_ = lean_ctor_get(v_m_u2082_1102_, 1);
v___x_1106_ = lean_nat_dec_le(v_size_1103_, v_size_1104_);
if (v___x_1106_ == 0)
{
lean_object* v___f_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v_buckets_1105_);
lean_dec_ref(v_m_u2082_1102_);
v___f_1107_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11));
v___x_1108_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1105_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1107_, v_inst_1099_, v_inst_1100_, v_m_u2081_1101_, v___x_1108_);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(v___x_1106_);
v___f_1111_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1111_, 0, v_inst_1099_);
lean_closure_set(v___f_1111_, 1, v_inst_1100_);
lean_closure_set(v___f_1111_, 2, v_m_u2082_1102_);
lean_closure_set(v___f_1111_, 3, v___x_1110_);
v___x_1112_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_u2081_1101_, v___f_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_m_u2081_1117_, lean_object* v_m_u2082_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(v_inst_1115_, v_inst_1116_, v_m_u2081_1117_, v_m_u2082_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_m_1122_, lean_object* v_l_1123_){
_start:
{
if (lean_obj_tag(v_l_1123_) == 0)
{
lean_dec_ref(v_inst_1121_);
lean_dec_ref(v_inst_1120_);
return v_m_1122_;
}
else
{
lean_object* v_head_1124_; lean_object* v_tail_1125_; lean_object* v_fst_1126_; lean_object* v_snd_1127_; lean_object* v___x_1128_; 
v_head_1124_ = lean_ctor_get(v_l_1123_, 0);
lean_inc(v_head_1124_);
v_tail_1125_ = lean_ctor_get(v_l_1123_, 1);
lean_inc(v_tail_1125_);
lean_dec_ref_known(v_l_1123_, 2);
v_fst_1126_ = lean_ctor_get(v_head_1124_, 0);
lean_inc(v_fst_1126_);
v_snd_1127_ = lean_ctor_get(v_head_1124_, 1);
lean_inc(v_snd_1127_);
lean_dec(v_head_1124_);
lean_inc_ref(v_inst_1121_);
lean_inc_ref(v_inst_1120_);
v___x_1128_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1120_, v_inst_1121_, v_m_1122_, v_fst_1126_, v_snd_1127_);
v_m_1122_ = v___x_1128_;
v_l_1123_ = v_tail_1125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_m_1134_, lean_object* v_l_1135_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1132_, v_inst_1133_, v_m_1134_, v_l_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_m_u2081_1139_, lean_object* v_m_u2082_1140_){
_start:
{
lean_object* v_size_1141_; lean_object* v_buckets_1142_; lean_object* v_size_1143_; lean_object* v_buckets_1144_; uint8_t v___x_1145_; 
v_size_1141_ = lean_ctor_get(v_m_u2081_1139_, 0);
v_buckets_1142_ = lean_ctor_get(v_m_u2081_1139_, 1);
v_size_1143_ = lean_ctor_get(v_m_u2082_1140_, 0);
v_buckets_1144_ = lean_ctor_get(v_m_u2082_1140_, 1);
v___x_1145_ = lean_nat_dec_le(v_size_1141_, v_size_1143_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_inc_ref(v_buckets_1144_);
lean_dec_ref(v_m_u2082_1140_);
v___x_1146_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1144_);
v___x_1147_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(v_inst_1137_, v_inst_1138_, v_m_u2081_1139_, v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc_ref(v_buckets_1142_);
lean_dec_ref(v_m_u2081_1139_);
v___x_1148_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1142_);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1137_, v_inst_1138_, v_m_u2082_1140_, v___x_1148_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_m_u2081_1154_, lean_object* v_m_u2082_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(v_inst_1152_, v_inst_1153_, v_m_u2081_1154_, v_m_u2082_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_m_1159_, lean_object* v_sofar_1160_, lean_object* v_k_1161_){
_start:
{
lean_object* v___x_1162_; 
lean_inc_ref(v_inst_1158_);
lean_inc_ref(v_inst_1157_);
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_1157_, v_inst_1158_, v_m_1159_, v_k_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_dec_ref(v_inst_1158_);
lean_dec_ref(v_inst_1157_);
return v_sofar_1160_;
}
else
{
lean_object* v_val_1163_; lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1166_; 
v_val_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_fst_1164_ = lean_ctor_get(v_val_1163_, 0);
lean_inc(v_fst_1164_);
v_snd_1165_ = lean_ctor_get(v_val_1163_, 1);
lean_inc(v_snd_1165_);
lean_dec(v_val_1163_);
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(v_inst_1157_, v_inst_1158_, v_sofar_1160_, v_fst_1164_, v_snd_1165_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_m_1169_, lean_object* v_sofar_1170_, lean_object* v_k_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1167_, v_inst_1168_, v_m_1169_, v_sofar_1170_, v_k_1171_);
lean_dec_ref(v_m_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_m_1177_, lean_object* v_sofar_1178_, lean_object* v_k_1179_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1175_, v_inst_1176_, v_m_1177_, v_sofar_1178_, v_k_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_m_1185_, lean_object* v_sofar_1186_, lean_object* v_k_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(v_00_u03b1_1181_, v_00_u03b2_1182_, v_inst_1183_, v_inst_1184_, v_m_1185_, v_sofar_1186_, v_k_1187_);
lean_dec_ref(v_m_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_m_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_buckets_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_buckets_1193_ = lean_ctor_get(v_m_1191_, 1);
lean_inc(v_a_1192_);
v___x_1194_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1190_, v_buckets_1193_, v_a_1192_);
v___x_1195_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1189_, v_a_1192_, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_m_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1196_, v_inst_1197_, v_m_1198_, v_a_1199_);
lean_dec_ref(v_m_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1203_, v_inst_1204_, v_m_1205_, v_a_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_00_u03b2_1209_, lean_object* v_inst_1210_, lean_object* v_inst_1211_, lean_object* v_m_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(v_00_u03b1_1208_, v_00_u03b2_1209_, v_inst_1210_, v_inst_1211_, v_m_1212_, v_a_1213_);
lean_dec_ref(v_m_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_m_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_buckets_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_buckets_1219_ = lean_ctor_get(v_m_1217_, 1);
lean_inc(v_a_1218_);
v___x_1220_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1216_, v_buckets_1219_, v_a_1218_);
v___x_1221_ = l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1215_, v_a_1218_, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_m_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_1222_, v_inst_1223_, v_m_1224_, v_a_1225_);
lean_dec_ref(v_m_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_m_1231_, lean_object* v_a_1232_, lean_object* v_h_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_1229_, v_inst_1230_, v_m_1231_, v_a_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_00_u03b2_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_m_1239_, lean_object* v_a_1240_, lean_object* v_h_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(v_00_u03b1_1235_, v_00_u03b2_1236_, v_inst_1237_, v_inst_1238_, v_m_1239_, v_a_1240_, v_h_1241_);
lean_dec_ref(v_m_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_fallback_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1243_, v_inst_1244_, v_m_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_inc(v_fallback_1247_);
return v_fallback_1247_;
}
else
{
lean_object* v_val_1249_; 
v_val_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1249_);
lean_dec_ref_known(v___x_1248_, 1);
return v_val_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_m_1252_, lean_object* v_a_1253_, lean_object* v_fallback_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_1250_, v_inst_1251_, v_m_1252_, v_a_1253_, v_fallback_1254_);
lean_dec(v_fallback_1254_);
lean_dec_ref(v_m_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_, lean_object* v_fallback_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_1258_, v_inst_1259_, v_m_1260_, v_a_1261_, v_fallback_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_m_1268_, lean_object* v_a_1269_, lean_object* v_fallback_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(v_00_u03b1_1264_, v_00_u03b2_1265_, v_inst_1266_, v_inst_1267_, v_m_1268_, v_a_1269_, v_fallback_1270_);
lean_dec(v_fallback_1270_);
lean_dec_ref(v_m_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1272_, v_inst_1273_, v_m_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_1279_ = l_panic___redArg(v_inst_1274_, v___x_1278_);
return v___x_1279_;
}
else
{
lean_object* v_val_1280_; 
v_val_1280_ = lean_ctor_get(v___x_1277_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v___x_1277_, 1);
return v_val_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_m_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_1281_, v_inst_1282_, v_inst_1283_, v_m_1284_, v_a_1285_);
lean_dec_ref(v_m_1284_);
lean_dec(v_inst_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_m_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_1289_, v_inst_1290_, v_inst_1291_, v_m_1292_, v_a_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_m_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(v_00_u03b1_1295_, v_00_u03b2_1296_, v_inst_1297_, v_inst_1298_, v_inst_1299_, v_m_1300_, v_a_1301_);
lean_dec_ref(v_m_1300_);
lean_dec(v_inst_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_m_1305_, lean_object* v_l_1306_){
_start:
{
if (lean_obj_tag(v_l_1306_) == 0)
{
lean_dec_ref(v_inst_1304_);
lean_dec_ref(v_inst_1303_);
return v_m_1305_;
}
else
{
lean_object* v_head_1307_; lean_object* v_tail_1308_; lean_object* v_fst_1309_; lean_object* v_snd_1310_; lean_object* v___x_1311_; 
v_head_1307_ = lean_ctor_get(v_l_1306_, 0);
lean_inc(v_head_1307_);
v_tail_1308_ = lean_ctor_get(v_l_1306_, 1);
lean_inc(v_tail_1308_);
lean_dec_ref_known(v_l_1306_, 2);
v_fst_1309_ = lean_ctor_get(v_head_1307_, 0);
lean_inc(v_fst_1309_);
v_snd_1310_ = lean_ctor_get(v_head_1307_, 1);
lean_inc(v_snd_1310_);
lean_dec(v_head_1307_);
lean_inc_ref(v_inst_1304_);
lean_inc_ref(v_inst_1303_);
v___x_1311_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1303_, v_inst_1304_, v_m_1305_, v_fst_1309_, v_snd_1310_);
v_m_1305_ = v___x_1311_;
v_l_1306_ = v_tail_1308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(lean_object* v_00_u03b1_1313_, lean_object* v_00_u03b2_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_m_1317_, lean_object* v_l_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(v_inst_1315_, v_inst_1316_, v_m_1317_, v_l_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_m_1322_, lean_object* v_l_1323_){
_start:
{
if (lean_obj_tag(v_l_1323_) == 0)
{
lean_dec_ref(v_inst_1321_);
lean_dec_ref(v_inst_1320_);
return v_m_1322_;
}
else
{
lean_object* v_head_1324_; lean_object* v_tail_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_head_1324_ = lean_ctor_get(v_l_1323_, 0);
lean_inc(v_head_1324_);
v_tail_1325_ = lean_ctor_get(v_l_1323_, 1);
lean_inc(v_tail_1325_);
lean_dec_ref_known(v_l_1323_, 2);
v___x_1326_ = lean_box(0);
lean_inc_ref(v_inst_1321_);
lean_inc_ref(v_inst_1320_);
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1320_, v_inst_1321_, v_m_1322_, v_head_1324_, v___x_1326_);
v_m_1322_ = v___x_1327_;
v_l_1323_ = v_tail_1325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(lean_object* v_00_u03b1_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_m_1332_, lean_object* v_l_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(v_inst_1330_, v_inst_1331_, v_m_1332_, v_l_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___redArg(lean_object* v_x_1335_, lean_object* v_h__1_1336_, lean_object* v_h__2_1337_){
_start:
{
if (lean_obj_tag(v_x_1335_) == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_h__2_1337_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_apply_1(v_h__1_1336_, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; lean_object* v___x_1341_; 
lean_dec(v_h__1_1336_);
v_val_1340_ = lean_ctor_get(v_x_1335_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v_x_1335_, 1);
v___x_1341_ = lean_apply_1(v_h__2_1337_, v_val_1340_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(lean_object* v_00_u03b1_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_a_1344_, lean_object* v_motive_1345_, lean_object* v_x_1346_, lean_object* v_h__1_1347_, lean_object* v_h__2_1348_){
_start:
{
if (lean_obj_tag(v_x_1346_) == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v_h__2_1348_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_apply_1(v_h__1_1347_, v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1352_; 
lean_dec(v_h__1_1347_);
v_val_1351_ = lean_ctor_get(v_x_1346_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_x_1346_, 1);
v___x_1352_ = lean_apply_1(v_h__2_1348_, v_val_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_a_1355_, lean_object* v_motive_1356_, lean_object* v_x_1357_, lean_object* v_h__1_1358_, lean_object* v_h__2_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(v_00_u03b1_1353_, v_00_u03b2_1354_, v_a_1355_, v_motive_1356_, v_x_1357_, v_h__1_1358_, v_h__2_1359_);
lean_dec(v_a_1355_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_1361_, lean_object* v_h__1_1362_, lean_object* v_h__2_1363_){
_start:
{
if (lean_obj_tag(v_x_1361_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_h__2_1363_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_apply_1(v_h__1_1362_, v___x_1364_);
return v___x_1365_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1367_; 
lean_dec(v_h__1_1362_);
v_val_1366_ = lean_ctor_get(v_x_1361_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v_x_1361_, 1);
v___x_1367_ = lean_apply_1(v_h__2_1363_, v_val_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_a_1370_, lean_object* v_motive_1371_, lean_object* v_x_1372_, lean_object* v_h__1_1373_, lean_object* v_h__2_1374_){
_start:
{
if (lean_obj_tag(v_x_1372_) == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_h__2_1374_);
v___x_1375_ = lean_box(0);
v___x_1376_ = lean_apply_1(v_h__1_1373_, v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v_val_1377_; lean_object* v___x_1378_; 
lean_dec(v_h__1_1373_);
v_val_1377_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v_x_1372_, 1);
v___x_1378_ = lean_apply_1(v_h__2_1374_, v_val_1377_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_a_1381_, lean_object* v_motive_1382_, lean_object* v_x_1383_, lean_object* v_h__1_1384_, lean_object* v_h__2_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_1379_, v_00_u03b2_1380_, v_a_1381_, v_motive_1382_, v_x_1383_, v_h__1_1384_, v_h__2_1385_);
lean_dec(v_a_1381_);
return v_res_1386_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(size_t v_x_1387_, lean_object* v_h__1_1388_){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_box_usize(v_x_1387_);
v___x_1390_ = lean_apply_2(v_h__1_1388_, v___x_1389_, lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_x_1387_ = stack[0].m_num;
lean_object* v_h__1_1388_ = stack[1].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(v_x_1387_, v_h__1_1388_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg___boxed(lean_object* v_x_1392_, lean_object* v_h__1_1393_){
_start:
{
size_t v_x_14__boxed_1394_; lean_object* v_res_1395_; 
v_x_14__boxed_1394_ = lean_unbox_usize(v_x_1392_);
lean_dec(v_x_1392_);
v_res_1395_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(v_x_14__boxed_1394_, v_h__1_1393_);
return v_res_1395_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(lean_object* v_00_u03b1_1396_, lean_object* v_00_u03b2_1397_, lean_object* v_data_1398_, lean_object* v_motive_1399_, size_t v_x_1400_, lean_object* v_h__1_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_box_usize(v_x_1400_);
v___x_1403_ = lean_apply_2(v_h__1_1401_, v___x_1402_, lean_box(0));
return v___x_1403_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_1398_ = stack[2].m_obj;
size_t v_x_1400_ = stack[4].m_num;
lean_object* v_h__1_1401_ = stack[5].m_obj;
lean_object* v_res_1404_;
v_res_1404_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(lean_box(0), lean_box(0), v_data_1398_, lean_box(0), v_x_1400_, v_h__1_1401_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_data_1407_, lean_object* v_motive_1408_, lean_object* v_x_1409_, lean_object* v_h__1_1410_){
_start:
{
size_t v_x_25__boxed_1411_; lean_object* v_res_1412_; 
v_x_25__boxed_1411_ = lean_unbox_usize(v_x_1409_);
lean_dec(v_x_1409_);
v_res_1412_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(v_00_u03b1_1405_, v_00_u03b2_1406_, v_data_1407_, v_motive_1408_, v_x_25__boxed_1411_, v_h__1_1410_);
lean_dec_ref(v_data_1407_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(lean_object* v_x_1413_, lean_object* v_h__1_1414_, lean_object* v_h__2_1415_){
_start:
{
if (lean_obj_tag(v_x_1413_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_dec(v_h__2_1415_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_apply_1(v_h__1_1414_, v___x_1416_);
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; lean_object* v___x_1419_; 
lean_dec(v_h__1_1414_);
v_val_1418_ = lean_ctor_get(v_x_1413_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v_x_1413_, 1);
v___x_1419_ = lean_apply_1(v_h__2_1415_, v_val_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(lean_object* v_00_u03b2_1420_, lean_object* v_motive_1421_, lean_object* v_x_1422_, lean_object* v_h__1_1423_, lean_object* v_h__2_1424_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_h__2_1424_);
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_apply_1(v_h__1_1423_, v___x_1425_);
return v___x_1426_;
}
else
{
lean_object* v_val_1427_; lean_object* v___x_1428_; 
lean_dec(v_h__1_1423_);
v_val_1427_ = lean_ctor_get(v_x_1422_, 0);
lean_inc(v_val_1427_);
lean_dec_ref_known(v_x_1422_, 1);
v___x_1428_ = lean_apply_1(v_h__2_1424_, v_val_1427_);
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_1429_, lean_object* v_h__1_1430_, lean_object* v_h__2_1431_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_h__2_1431_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_apply_1(v_h__1_1430_, v___x_1432_);
return v___x_1433_;
}
else
{
lean_object* v_val_1434_; lean_object* v___x_1435_; 
lean_dec(v_h__1_1430_);
v_val_1434_ = lean_ctor_get(v_x_1429_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v_x_1429_, 1);
v___x_1435_ = lean_apply_1(v_h__2_1431_, v_val_1434_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_1436_, lean_object* v_motive_1437_, lean_object* v_x_1438_, lean_object* v_h__1_1439_, lean_object* v_h__2_1440_){
_start:
{
if (lean_obj_tag(v_x_1438_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec(v_h__2_1440_);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_apply_1(v_h__1_1439_, v___x_1441_);
return v___x_1442_;
}
else
{
lean_object* v_val_1443_; lean_object* v___x_1444_; 
lean_dec(v_h__1_1439_);
v_val_1443_ = lean_ctor_get(v_x_1438_, 0);
lean_inc(v_val_1443_);
lean_dec_ref_known(v_x_1438_, 1);
v___x_1444_ = lean_apply_1(v_h__2_1440_, v_val_1443_);
return v___x_1444_;
}
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(size_t v_x_1445_, lean_object* v_h__1_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_box_usize(v_x_1445_);
v___x_1448_ = lean_apply_2(v_h__1_1446_, v___x_1447_, lean_box(0));
return v___x_1448_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_x_1445_ = stack[0].m_num;
lean_object* v_h__1_1446_ = stack[1].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(v_x_1445_, v_h__1_1446_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(lean_object* v_x_1450_, lean_object* v_h__1_1451_){
_start:
{
size_t v_x_14__boxed_1452_; lean_object* v_res_1453_; 
v_x_14__boxed_1452_ = lean_unbox_usize(v_x_1450_);
lean_dec(v_x_1450_);
v_res_1453_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(v_x_14__boxed_1452_, v_h__1_1451_);
return v_res_1453_;
}
}
lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object* v_00_u03b1_1454_, lean_object* v_00_u03b2_1455_, lean_object* v_buckets_1456_, lean_object* v_motive_1457_, size_t v_x_1458_, lean_object* v_h__1_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_box_usize(v_x_1458_);
v___x_1461_ = lean_apply_2(v_h__1_1459_, v___x_1460_, lean_box(0));
return v___x_1461_;
}
}
LEAN_EXPORT void l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_buckets_1456_ = stack[2].m_obj;
size_t v_x_1458_ = stack[4].m_num;
lean_object* v_h__1_1459_ = stack[5].m_obj;
lean_object* v_res_1462_;
v_res_1462_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_box(0), lean_box(0), v_buckets_1456_, lean_box(0), v_x_1458_, v_h__1_1459_);
stack->m_obj
 = v_res_1462_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(lean_object* v_00_u03b1_1463_, lean_object* v_00_u03b2_1464_, lean_object* v_buckets_1465_, lean_object* v_motive_1466_, lean_object* v_x_1467_, lean_object* v_h__1_1468_){
_start:
{
size_t v_x_25__boxed_1469_; lean_object* v_res_1470_; 
v_x_25__boxed_1469_ = lean_unbox_usize(v_x_1467_);
lean_dec(v_x_1467_);
v_res_1470_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(v_00_u03b1_1463_, v_00_u03b2_1464_, v_buckets_1465_, v_motive_1466_, v_x_25__boxed_1469_, v_h__1_1468_);
lean_dec_ref(v_buckets_1465_);
return v_res_1470_;
}
}
lean_object* runtime_initialize_Init_Data_Array_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_HashesTo(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Model(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
