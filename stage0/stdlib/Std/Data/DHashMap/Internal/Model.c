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
size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_137_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_self_135_, v___x_140_, v___x_141_, v___x_136_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_self_135_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_withComputedSize(lean_object* v_00_u03b1_144_, lean_object* v_00_u03b2_145_, lean_object* v_self_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_self_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_as_150_, size_t v_i_151_, size_t v_stop_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___redArg(v_as_150_, v_i_151_, v_stop_152_, v_b_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0___boxed(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_as_157_, lean_object* v_i_158_, lean_object* v_stop_159_, lean_object* v_b_160_){
_start:
{
size_t v_i_boxed_161_; size_t v_stop_boxed_162_; lean_object* v_res_163_; 
v_i_boxed_161_ = lean_unbox_usize(v_i_158_);
lean_dec(v_i_158_);
v_stop_boxed_162_ = lean_unbox_usize(v_stop_159_);
lean_dec(v_stop_159_);
v_res_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_withComputedSize_spec__0(v_00_u03b1_155_, v_00_u03b2_156_, v_as_157_, v_i_boxed_161_, v_stop_boxed_162_, v_b_160_);
lean_dec_ref(v_as_157_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0(lean_object* v_inst_164_, lean_object* v_a_165_, lean_object* v_b_166_, lean_object* v_l_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_164_, v_a_165_, v_b_166_, v_l_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_m_171_, lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
lean_object* v_size_174_; lean_object* v_buckets_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_184_; 
v_size_174_ = lean_ctor_get(v_m_171_, 0);
v_buckets_175_ = lean_ctor_get(v_m_171_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_m_171_);
if (v_isSharedCheck_184_ == 0)
{
v___x_177_ = v_m_171_;
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_buckets_175_);
lean_inc(v_size_174_);
lean_dec(v_m_171_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
lean_inc(v_a_172_);
v___f_179_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_179_, 0, v_inst_169_);
lean_closure_set(v___f_179_, 1, v_a_172_);
lean_closure_set(v___f_179_, 2, v_b_173_);
v___x_180_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_170_, v_buckets_175_, v_a_172_, v___f_179_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_180_);
v___x_182_ = v___x_177_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_size_174_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_replace_u2098(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_m_189_, lean_object* v_a_190_, lean_object* v_b_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(v_inst_187_, v_inst_188_, v_m_189_, v_a_190_, v_b_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0(lean_object* v_a_193_, lean_object* v_b_194_, lean_object* v_l_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_196_, 0, v_a_193_);
lean_ctor_set(v___x_196_, 1, v_b_194_);
lean_ctor_set(v___x_196_, 2, v_l_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(lean_object* v_inst_197_, lean_object* v_m_198_, lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
lean_object* v_size_201_; lean_object* v_buckets_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_213_; 
v_size_201_ = lean_ctor_get(v_m_198_, 0);
v_buckets_202_ = lean_ctor_get(v_m_198_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_m_198_);
if (v_isSharedCheck_213_ == 0)
{
v___x_204_ = v_m_198_;
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_buckets_202_);
lean_inc(v_size_201_);
lean_dec(v_m_198_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
lean_inc(v_a_199_);
v___f_206_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg___lam__0), 3, 2);
lean_closure_set(v___f_206_, 0, v_a_199_);
lean_closure_set(v___f_206_, 1, v_b_200_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_size_201_, v___x_207_);
lean_dec(v_size_201_);
v___x_209_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_197_, v_buckets_202_, v_a_199_, v___f_206_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_209_);
lean_ctor_set(v___x_204_, 0, v___x_208_);
v___x_211_ = v___x_204_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_m_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_217_, v_m_218_, v_a_219_, v_b_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___boxed(lean_object* v_00_u03b1_222_, lean_object* v_00_u03b2_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_m_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098(v_00_u03b1_222_, v_00_u03b2_223_, v_inst_224_, v_inst_225_, v_m_226_, v_a_227_, v_b_228_);
lean_dec_ref(v_inst_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_buckets_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_buckets_234_ = lean_ctor_get(v_m_232_, 1);
lean_inc(v_a_233_);
v___x_235_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_231_, v_buckets_234_, v_a_233_);
v___x_236_ = l_Std_DHashMap_Internal_AssocList_getCast_x3f___redArg(v_inst_230_, v_a_233_, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg___boxed(lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_m_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_237_, v_inst_238_, v_m_239_, v_a_240_);
lean_dec_ref(v_m_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_m_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_244_, v_inst_246_, v_m_247_, v_a_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___boxed(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_inst_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_m_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098(v_00_u03b1_250_, v_00_u03b2_251_, v_inst_252_, v_inst_253_, v_inst_254_, v_m_255_, v_a_256_);
lean_dec_ref(v_m_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_m_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_buckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_buckets_262_ = lean_ctor_get(v_m_260_, 1);
lean_inc(v_a_261_);
v___x_263_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_259_, v_buckets_262_, v_a_261_);
v___x_264_ = l_Std_DHashMap_Internal_AssocList_getKey_x3f___redArg(v_inst_258_, v_a_261_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg___boxed(lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_265_, v_inst_266_, v_m_267_, v_a_268_);
lean_dec_ref(v_m_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(lean_object* v_00_u03b1_270_, lean_object* v_00_u03b2_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_m_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_272_, v_inst_273_, v_m_274_, v_a_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___boxed(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_m_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098(v_00_u03b1_277_, v_00_u03b2_278_, v_inst_279_, v_inst_280_, v_m_281_, v_a_282_);
lean_dec_ref(v_m_281_);
return v_res_283_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_buckets_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_buckets_288_ = lean_ctor_get(v_m_286_, 1);
lean_inc(v_a_287_);
v___x_289_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_285_, v_buckets_288_, v_a_287_);
v___x_290_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_284_, v_a_287_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg___boxed(lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_291_, v_inst_292_, v_m_293_, v_a_294_);
lean_dec_ref(v_m_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_m_301_, lean_object* v_a_302_){
_start:
{
uint8_t v___x_303_; 
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_299_, v_inst_300_, v_m_301_, v_a_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___boxed(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_m_308_, lean_object* v_a_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098(v_00_u03b1_304_, v_00_u03b2_305_, v_inst_306_, v_inst_307_, v_m_308_, v_a_309_);
lean_dec_ref(v_m_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_m_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_buckets_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_buckets_316_ = lean_ctor_get(v_m_314_, 1);
lean_inc(v_a_315_);
v___x_317_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_313_, v_buckets_316_, v_a_315_);
v___x_318_ = l_Std_DHashMap_Internal_AssocList_getCast___redArg(v_inst_312_, v_a_315_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg___boxed(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_m_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(v_inst_319_, v_inst_320_, v_m_321_, v_a_322_);
lean_dec_ref(v_m_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098(lean_object* v_00_u03b1_324_, lean_object* v_00_u03b2_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_h_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098___redArg(v_inst_326_, v_inst_328_, v_m_329_, v_a_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_u2098___boxed(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_m_338_, lean_object* v_a_339_, lean_object* v_h_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DHashMap_Internal_Raw_u2080_get_u2098(v_00_u03b1_333_, v_00_u03b2_334_, v_inst_335_, v_inst_336_, v_inst_337_, v_m_338_, v_a_339_, v_h_340_);
lean_dec_ref(v_m_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_m_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_buckets_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_buckets_346_ = lean_ctor_get(v_m_344_, 1);
lean_inc(v_a_345_);
v___x_347_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_343_, v_buckets_346_, v_a_345_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_getEntry___redArg(v_inst_342_, v_a_345_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg___boxed(lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_m_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(v_inst_349_, v_inst_350_, v_m_351_, v_a_352_);
lean_dec_ref(v_m_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_m_358_, lean_object* v_a_359_, lean_object* v_h_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___redArg(v_inst_356_, v_inst_357_, v_m_358_, v_a_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098___boxed(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_m_366_, lean_object* v_a_367_, lean_object* v_h_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_u2098(v_00_u03b1_362_, v_00_u03b2_363_, v_inst_364_, v_inst_365_, v_m_366_, v_a_367_, v_h_368_);
lean_dec_ref(v_m_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_m_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_buckets_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_buckets_374_ = lean_ctor_get(v_m_372_, 1);
lean_inc(v_a_373_);
v___x_375_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_371_, v_buckets_374_, v_a_373_);
v___x_376_ = l_Std_DHashMap_Internal_AssocList_getEntry_x3f___redArg(v_inst_370_, v_a_373_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg___boxed(lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_377_, v_inst_378_, v_m_379_, v_a_380_);
lean_dec_ref(v_m_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_m_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_384_, v_inst_385_, v_m_386_, v_a_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___boxed(lean_object* v_00_u03b1_389_, lean_object* v_00_u03b2_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_m_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098(v_00_u03b1_389_, v_00_u03b2_390_, v_inst_391_, v_inst_392_, v_m_393_, v_a_394_);
lean_dec_ref(v_m_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_m_398_, lean_object* v_a_399_, lean_object* v_fallback_400_){
_start:
{
lean_object* v_buckets_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_buckets_401_ = lean_ctor_get(v_m_398_, 1);
lean_inc(v_a_399_);
v___x_402_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_397_, v_buckets_401_, v_a_399_);
v___x_403_ = l_Std_DHashMap_Internal_AssocList_getEntryD___redArg(v_inst_396_, v_a_399_, v_fallback_400_, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg___boxed(lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_m_406_, lean_object* v_a_407_, lean_object* v_fallback_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(v_inst_404_, v_inst_405_, v_m_406_, v_a_407_, v_fallback_408_);
lean_dec_ref(v_fallback_408_);
lean_dec_ref(v_m_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_m_414_, lean_object* v_a_415_, lean_object* v_fallback_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___redArg(v_inst_412_, v_inst_413_, v_m_414_, v_a_415_, v_fallback_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098___boxed(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_m_422_, lean_object* v_a_423_, lean_object* v_fallback_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD_u2098(v_00_u03b1_418_, v_00_u03b2_419_, v_inst_420_, v_inst_421_, v_m_422_, v_a_423_, v_fallback_424_);
lean_dec_ref(v_fallback_424_);
lean_dec_ref(v_m_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_m_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_buckets_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_buckets_431_ = lean_ctor_get(v_m_429_, 1);
lean_inc(v_a_430_);
v___x_432_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_427_, v_buckets_431_, v_a_430_);
v___x_433_ = l_Std_DHashMap_Internal_AssocList_getEntry_x21___redArg(v_inst_426_, v_a_430_, v_inst_428_, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg___boxed(lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_m_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(v_inst_434_, v_inst_435_, v_inst_436_, v_m_437_, v_a_438_);
lean_dec_ref(v_m_437_);
lean_dec_ref(v_inst_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_m_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___redArg(v_inst_442_, v_inst_443_, v_inst_444_, v_m_445_, v_a_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098___boxed(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_m_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21_u2098(v_00_u03b1_448_, v_00_u03b2_449_, v_inst_450_, v_inst_451_, v_inst_452_, v_m_453_, v_a_454_);
lean_dec_ref(v_m_453_);
lean_dec_ref(v_inst_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_m_458_, lean_object* v_a_459_, lean_object* v_fallback_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_456_, v_inst_457_, v_m_458_, v_a_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_inc(v_fallback_460_);
return v_fallback_460_;
}
else
{
lean_object* v_val_462_; 
v_val_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_val_462_);
lean_dec_ref_known(v___x_461_, 1);
return v_val_462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg___boxed(lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_m_465_, lean_object* v_a_466_, lean_object* v_fallback_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(v_inst_463_, v_inst_464_, v_m_465_, v_a_466_, v_fallback_467_);
lean_dec(v_fallback_467_);
lean_dec_ref(v_m_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_m_474_, lean_object* v_a_475_, lean_object* v_fallback_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___redArg(v_inst_471_, v_inst_473_, v_m_474_, v_a_475_, v_fallback_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD_u2098___boxed(lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_fallback_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_getD_u2098(v_00_u03b1_478_, v_00_u03b2_479_, v_inst_480_, v_inst_481_, v_inst_482_, v_m_483_, v_a_484_, v_fallback_485_);
lean_dec(v_fallback_485_);
lean_dec_ref(v_m_483_);
return v_res_486_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_490_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__2));
v___x_491_ = lean_unsigned_to_nat(14u);
v___x_492_ = lean_unsigned_to_nat(22u);
v___x_493_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__1));
v___x_494_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__0));
v___x_495_ = l_mkPanicMessageWithDecl(v___x_494_, v___x_493_, v___x_492_, v___x_491_, v___x_490_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f_u2098___redArg(v_inst_496_, v_inst_497_, v_m_498_, v_a_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_503_ = l_panic___redArg(v_inst_500_, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_val_504_; 
v_val_504_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_501_, 1);
return v_val_504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___boxed(lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_m_507_, lean_object* v_a_508_, lean_object* v_inst_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(v_inst_505_, v_inst_506_, v_m_507_, v_a_508_, v_inst_509_);
lean_dec(v_inst_509_);
lean_dec_ref(v_m_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_m_516_, lean_object* v_a_517_, lean_object* v_inst_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg(v_inst_513_, v_inst_515_, v_m_516_, v_a_517_, v_inst_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___boxed(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_m_525_, lean_object* v_a_526_, lean_object* v_inst_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098(v_00_u03b1_520_, v_00_u03b2_521_, v_inst_522_, v_inst_523_, v_inst_524_, v_m_525_, v_a_526_, v_inst_527_);
lean_dec(v_inst_527_);
lean_dec_ref(v_m_525_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_m_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_buckets_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_buckets_533_ = lean_ctor_get(v_m_531_, 1);
lean_inc(v_a_532_);
v___x_534_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_530_, v_buckets_533_, v_a_532_);
v___x_535_ = l_Std_DHashMap_Internal_AssocList_getKey___redArg(v_inst_529_, v_a_532_, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg___boxed(lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(v_inst_536_, v_inst_537_, v_m_538_, v_a_539_);
lean_dec_ref(v_m_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(lean_object* v_00_u03b1_541_, lean_object* v_00_u03b2_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_m_545_, lean_object* v_a_546_, lean_object* v_h_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___redArg(v_inst_543_, v_inst_544_, v_m_545_, v_a_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098___boxed(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_m_553_, lean_object* v_a_554_, lean_object* v_h_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_u2098(v_00_u03b1_549_, v_00_u03b2_550_, v_inst_551_, v_inst_552_, v_m_553_, v_a_554_, v_h_555_);
lean_dec_ref(v_m_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_m_559_, lean_object* v_a_560_, lean_object* v_fallback_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_557_, v_inst_558_, v_m_559_, v_a_560_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_inc(v_fallback_561_);
return v_fallback_561_;
}
else
{
lean_object* v_val_563_; 
v_val_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_563_);
lean_dec_ref_known(v___x_562_, 1);
return v_val_563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg___boxed(lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_m_566_, lean_object* v_a_567_, lean_object* v_fallback_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(v_inst_564_, v_inst_565_, v_m_566_, v_a_567_, v_fallback_568_);
lean_dec(v_fallback_568_);
lean_dec_ref(v_m_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_m_574_, lean_object* v_a_575_, lean_object* v_fallback_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___redArg(v_inst_572_, v_inst_573_, v_m_574_, v_a_575_, v_fallback_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098___boxed(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_m_582_, lean_object* v_a_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD_u2098(v_00_u03b1_578_, v_00_u03b2_579_, v_inst_580_, v_inst_581_, v_m_582_, v_a_583_, v_fallback_584_);
lean_dec(v_fallback_584_);
lean_dec_ref(v_m_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_m_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f_u2098___redArg(v_inst_586_, v_inst_587_, v_m_589_, v_a_590_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_593_ = l_panic___redArg(v_inst_588_, v___x_592_);
return v___x_593_;
}
else
{
lean_object* v_val_594_; 
v_val_594_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_val_594_);
lean_dec_ref_known(v___x_591_, 1);
return v_val_594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg___boxed(lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_m_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(v_inst_595_, v_inst_596_, v_inst_597_, v_m_598_, v_a_599_);
lean_dec_ref(v_m_598_);
lean_dec(v_inst_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(lean_object* v_00_u03b1_601_, lean_object* v_00_u03b2_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_m_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___redArg(v_inst_603_, v_inst_604_, v_inst_605_, v_m_606_, v_a_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098___boxed(lean_object* v_00_u03b1_609_, lean_object* v_00_u03b2_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_m_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21_u2098(v_00_u03b1_609_, v_00_u03b2_610_, v_inst_611_, v_inst_612_, v_inst_613_, v_m_614_, v_a_615_);
lean_dec_ref(v_m_614_);
lean_dec(v_inst_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_m_619_, lean_object* v_a_620_, lean_object* v_b_621_){
_start:
{
uint8_t v___x_622_; 
lean_inc(v_a_620_);
lean_inc_ref(v_inst_618_);
lean_inc_ref(v_inst_617_);
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_617_, v_inst_618_, v_m_619_, v_a_620_);
if (v___x_622_ == 0)
{
lean_object* v_val_623_; lean_object* v_size_624_; lean_object* v_buckets_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
lean_dec_ref(v_inst_617_);
lean_inc_ref(v_inst_618_);
v_val_623_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_618_, v_m_619_, v_a_620_, v_b_621_);
v_size_624_ = lean_ctor_get(v_val_623_, 0);
lean_inc(v_size_624_);
v_buckets_625_ = lean_ctor_get(v_val_623_, 1);
lean_inc_ref(v_buckets_625_);
v___x_626_ = lean_unsigned_to_nat(4u);
v___x_627_ = lean_nat_mul(v_size_624_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(3u);
v___x_629_ = lean_nat_div(v___x_627_, v___x_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_array_get_size(v_buckets_625_);
v___x_631_ = lean_nat_dec_le(v___x_629_, v___x_630_);
lean_dec(v___x_629_);
if (v___x_631_ == 0)
{
lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
v_isSharedCheck_639_ = !lean_is_exclusive(v_val_623_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_640_ = lean_ctor_get(v_val_623_, 1);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_val_623_, 0);
lean_dec(v_unused_641_);
v___x_633_ = v_val_623_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_dec(v_val_623_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_val_635_; lean_object* v___x_637_; 
v_val_635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_618_, v_buckets_625_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_val_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_size_624_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_val_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
lean_dec_ref(v_buckets_625_);
lean_dec(v_size_624_);
lean_dec_ref(v_inst_618_);
return v_val_623_;
}
}
else
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_DHashMap_Internal_Raw_u2080_replace_u2098___redArg(v_inst_617_, v_inst_618_, v_m_619_, v_a_620_, v_b_621_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert_u2098(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_inst_645_, lean_object* v_inst_646_, lean_object* v_m_647_, lean_object* v_a_648_, lean_object* v_b_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(v_inst_645_, v_inst_646_, v_m_647_, v_a_648_, v_b_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
uint8_t v___x_656_; 
lean_inc(v_a_654_);
lean_inc_ref(v_inst_652_);
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_651_, v_inst_652_, v_m_653_, v_a_654_);
if (v___x_656_ == 0)
{
lean_object* v_val_657_; lean_object* v_size_658_; lean_object* v_buckets_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
lean_inc_ref(v_inst_652_);
v_val_657_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_652_, v_m_653_, v_a_654_, v_b_655_);
v_size_658_ = lean_ctor_get(v_val_657_, 0);
lean_inc(v_size_658_);
v_buckets_659_ = lean_ctor_get(v_val_657_, 1);
lean_inc_ref(v_buckets_659_);
v___x_660_ = lean_unsigned_to_nat(4u);
v___x_661_ = lean_nat_mul(v_size_658_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = lean_nat_div(v___x_661_, v___x_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_array_get_size(v_buckets_659_);
v___x_665_ = lean_nat_dec_le(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
if (v___x_665_ == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
v_isSharedCheck_673_ = !lean_is_exclusive(v_val_657_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; 
v_unused_674_ = lean_ctor_get(v_val_657_, 1);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v_val_657_, 0);
lean_dec(v_unused_675_);
v___x_667_ = v_val_657_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_val_657_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_val_669_; lean_object* v___x_671_; 
v_val_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_652_, v_buckets_659_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v_val_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_size_658_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_val_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_dec_ref(v_buckets_659_);
lean_dec(v_size_658_);
lean_dec_ref(v_inst_652_);
return v_val_657_;
}
}
else
{
lean_dec(v_b_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_inst_652_);
return v_m_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_m_680_, lean_object* v_a_681_, lean_object* v_b_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew_u2098___redArg(v_inst_678_, v_inst_679_, v_m_680_, v_a_681_, v_b_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0(lean_object* v_inst_684_, lean_object* v_a_685_, lean_object* v_l_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Std_DHashMap_Internal_AssocList_erase___redArg(v_inst_684_, v_a_685_, v_l_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_m_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_size_692_; lean_object* v_buckets_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_704_; 
v_size_692_ = lean_ctor_get(v_m_690_, 0);
v_buckets_693_ = lean_ctor_get(v_m_690_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_m_690_);
if (v_isSharedCheck_704_ == 0)
{
v___x_695_ = v_m_690_;
v_isShared_696_ = v_isSharedCheck_704_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_buckets_693_);
lean_inc(v_size_692_);
lean_dec(v_m_690_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_704_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
lean_inc(v_a_691_);
v___f_697_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_697_, 0, v_inst_688_);
lean_closure_set(v___f_697_, 1, v_a_691_);
v___x_698_ = lean_unsigned_to_nat(1u);
v___x_699_ = lean_nat_sub(v_size_692_, v___x_698_);
lean_dec(v_size_692_);
v___x_700_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_689_, v_buckets_693_, v_a_691_, v___f_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___x_700_);
lean_ctor_set(v___x_695_, 0, v___x_699_);
v___x_702_ = v___x_695_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b2_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_m_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(v_inst_707_, v_inst_708_, v_m_709_, v_a_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
uint8_t v___x_716_; 
lean_inc(v_a_715_);
lean_inc_ref(v_inst_713_);
lean_inc_ref(v_inst_712_);
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_712_, v_inst_713_, v_m_714_, v_a_715_);
if (v___x_716_ == 0)
{
lean_dec(v_a_715_);
lean_dec_ref(v_inst_713_);
lean_dec_ref(v_inst_712_);
return v_m_714_;
}
else
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098aux___redArg(v_inst_712_, v_inst_713_, v_m_714_, v_a_715_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase_u2098(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_inst_720_, lean_object* v_inst_721_, lean_object* v_m_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_erase_u2098___redArg(v_inst_720_, v_inst_721_, v_m_722_, v_a_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0(lean_object* v_inst_725_, lean_object* v_a_726_, lean_object* v_f_727_, lean_object* v_l_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Std_DHashMap_Internal_AssocList_alter___redArg(v_inst_725_, v_a_726_, v_f_727_, v_l_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_, lean_object* v_f_734_){
_start:
{
uint8_t v___x_735_; 
lean_inc(v_a_733_);
lean_inc_ref(v_inst_731_);
lean_inc_ref(v_inst_730_);
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_730_, v_inst_731_, v_m_732_, v_a_733_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v_inst_730_);
v___x_736_ = lean_box(0);
v___x_737_ = lean_apply_1(v_f_734_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_dec(v_a_733_);
lean_dec_ref(v_inst_731_);
return v_m_732_;
}
else
{
lean_object* v_val_738_; lean_object* v_val_739_; lean_object* v_size_740_; lean_object* v_buckets_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_737_, 1);
lean_inc_ref(v_inst_731_);
v_val_739_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_731_, v_m_732_, v_a_733_, v_val_738_);
v_size_740_ = lean_ctor_get(v_val_739_, 0);
lean_inc(v_size_740_);
v_buckets_741_ = lean_ctor_get(v_val_739_, 1);
lean_inc_ref(v_buckets_741_);
v___x_742_ = lean_unsigned_to_nat(4u);
v___x_743_ = lean_nat_mul(v_size_740_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(3u);
v___x_745_ = lean_nat_div(v___x_743_, v___x_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_array_get_size(v_buckets_741_);
v___x_747_ = lean_nat_dec_le(v___x_745_, v___x_746_);
lean_dec(v___x_745_);
if (v___x_747_ == 0)
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_isSharedCheck_755_ = !lean_is_exclusive(v_val_739_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; 
v_unused_756_ = lean_ctor_get(v_val_739_, 1);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_val_739_, 0);
lean_dec(v_unused_757_);
v___x_749_ = v_val_739_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_dec(v_val_739_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_val_751_; lean_object* v___x_753_; 
v_val_751_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_731_, v_buckets_741_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_val_751_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_size_740_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_val_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_dec_ref(v_buckets_741_);
lean_dec(v_size_740_);
lean_dec_ref(v_inst_731_);
return v_val_739_;
}
}
}
else
{
lean_object* v_size_758_; lean_object* v_buckets_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_775_; 
v_size_758_ = lean_ctor_get(v_m_732_, 0);
v_buckets_759_ = lean_ctor_get(v_m_732_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_m_732_);
if (v_isSharedCheck_775_ == 0)
{
v___x_761_ = v_m_732_;
v_isShared_762_ = v_isSharedCheck_775_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_buckets_759_);
lean_inc(v_size_758_);
lean_dec(v_m_732_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_775_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___f_763_; lean_object* v_buckets_x27_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
lean_inc_n(v_a_733_, 2);
lean_inc_ref(v_inst_730_);
v___f_763_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_763_, 0, v_inst_730_);
lean_closure_set(v___f_763_, 1, v_a_733_);
lean_closure_set(v___f_763_, 2, v_f_734_);
lean_inc_ref(v_inst_731_);
v_buckets_x27_764_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_731_, v_buckets_759_, v_a_733_, v___f_763_);
lean_inc_ref(v_buckets_x27_764_);
v___x_765_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_764_);
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_730_, v_inst_731_, v___x_765_, v_a_733_);
lean_dec_ref(v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_sub(v_size_758_, v___x_767_);
lean_dec(v_size_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_buckets_x27_764_);
lean_ctor_set(v___x_761_, 0, v___x_768_);
v___x_770_ = v___x_761_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_buckets_x27_764_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
else
{
lean_object* v___x_773_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_buckets_x27_764_);
v___x_773_ = v___x_761_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_size_758_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_buckets_x27_764_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_alter_u2098(lean_object* v_00_u03b1_776_, lean_object* v_00_u03b2_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_m_781_, lean_object* v_a_782_, lean_object* v_f_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(v_inst_778_, v_inst_779_, v_m_781_, v_a_782_, v_f_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0(lean_object* v_f_785_, lean_object* v_x_786_){
_start:
{
if (lean_obj_tag(v_x_786_) == 0)
{
lean_dec(v_f_785_);
return v_x_786_;
}
else
{
lean_object* v_val_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_val_787_ = lean_ctor_get(v_x_786_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_786_);
if (v_isSharedCheck_795_ == 0)
{
v___x_789_ = v_x_786_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_val_787_);
lean_dec(v_x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_apply_1(v_f_785_, v_val_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_m_798_, lean_object* v_a_799_, lean_object* v_f_800_){
_start:
{
lean_object* v___f_801_; lean_object* v___x_802_; 
v___f_801_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_801_, 0, v_f_800_);
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_alter_u2098___redArg(v_inst_796_, v_inst_797_, v_m_798_, v_a_799_, v___f_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_modify_u2098(lean_object* v_00_u03b1_803_, lean_object* v_00_u03b2_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_m_808_, lean_object* v_a_809_, lean_object* v_f_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_modify_u2098___redArg(v_inst_805_, v_inst_806_, v_m_808_, v_a_809_, v_f_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0(lean_object* v_inst_812_, lean_object* v_a_813_, lean_object* v_f_814_, lean_object* v_l_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DHashMap_Internal_AssocList_Const_alter___redArg(v_inst_812_, v_a_813_, v_f_814_, v_l_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_m_819_, lean_object* v_a_820_, lean_object* v_f_821_){
_start:
{
uint8_t v___x_822_; 
lean_inc(v_a_820_);
lean_inc_ref(v_inst_818_);
lean_inc_ref(v_inst_817_);
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_817_, v_inst_818_, v_m_819_, v_a_820_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_dec_ref(v_inst_817_);
v___x_823_ = lean_box(0);
v___x_824_ = lean_apply_1(v_f_821_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_dec(v_a_820_);
lean_dec_ref(v_inst_818_);
return v_m_819_;
}
else
{
lean_object* v_val_825_; lean_object* v_val_826_; lean_object* v_size_827_; lean_object* v_buckets_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_val_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v___x_824_, 1);
lean_inc_ref(v_inst_818_);
v_val_826_ = l_Std_DHashMap_Internal_Raw_u2080_cons_u2098___redArg(v_inst_818_, v_m_819_, v_a_820_, v_val_825_);
v_size_827_ = lean_ctor_get(v_val_826_, 0);
lean_inc(v_size_827_);
v_buckets_828_ = lean_ctor_get(v_val_826_, 1);
lean_inc_ref(v_buckets_828_);
v___x_829_ = lean_unsigned_to_nat(4u);
v___x_830_ = lean_nat_mul(v_size_827_, v___x_829_);
v___x_831_ = lean_unsigned_to_nat(3u);
v___x_832_ = lean_nat_div(v___x_830_, v___x_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_array_get_size(v_buckets_828_);
v___x_834_ = lean_nat_dec_le(v___x_832_, v___x_833_);
lean_dec(v___x_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v_val_826_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; 
v_unused_843_ = lean_ctor_get(v_val_826_, 1);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_val_826_, 0);
lean_dec(v_unused_844_);
v___x_836_ = v_val_826_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_val_826_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_val_838_; lean_object* v___x_840_; 
v_val_838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_818_, v_buckets_828_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_val_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_size_827_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_val_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_dec_ref(v_buckets_828_);
lean_dec(v_size_827_);
lean_dec_ref(v_inst_818_);
return v_val_826_;
}
}
}
else
{
lean_object* v_size_845_; lean_object* v_buckets_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_862_; 
v_size_845_ = lean_ctor_get(v_m_819_, 0);
v_buckets_846_ = lean_ctor_get(v_m_819_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_m_819_);
if (v_isSharedCheck_862_ == 0)
{
v___x_848_ = v_m_819_;
v_isShared_849_ = v_isSharedCheck_862_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_buckets_846_);
lean_inc(v_size_845_);
lean_dec(v_m_819_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_862_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___f_850_; lean_object* v_buckets_x27_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
lean_inc_n(v_a_820_, 2);
lean_inc_ref(v_inst_817_);
v___f_850_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg___lam__0), 4, 3);
lean_closure_set(v___f_850_, 0, v_inst_817_);
lean_closure_set(v___f_850_, 1, v_a_820_);
lean_closure_set(v___f_850_, 2, v_f_821_);
lean_inc_ref(v_inst_818_);
v_buckets_x27_851_ = l_Std_DHashMap_Internal_updateBucket___redArg(v_inst_818_, v_buckets_846_, v_a_820_, v___f_850_);
lean_inc_ref(v_buckets_x27_851_);
v___x_852_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v_buckets_x27_851_);
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_817_, v_inst_818_, v___x_852_, v_a_820_);
lean_dec_ref(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = lean_unsigned_to_nat(1u);
v___x_855_ = lean_nat_sub(v_size_845_, v___x_854_);
lean_dec(v_size_845_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_buckets_x27_851_);
lean_ctor_set(v___x_848_, 0, v___x_855_);
v___x_857_ = v___x_848_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_buckets_x27_851_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_buckets_x27_851_);
v___x_860_ = v___x_848_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_size_845_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_buckets_x27_851_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098(lean_object* v_00_u03b1_863_, lean_object* v_00_u03b2_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_m_867_, lean_object* v_a_868_, lean_object* v_f_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(v_inst_865_, v_inst_866_, v_m_867_, v_a_868_, v_f_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0(lean_object* v_f_871_, lean_object* v_option_872_){
_start:
{
if (lean_obj_tag(v_option_872_) == 0)
{
lean_dec(v_f_871_);
return v_option_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_881_; 
v_val_873_ = lean_ctor_get(v_option_872_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_option_872_);
if (v_isSharedCheck_881_ == 0)
{
v___x_875_ = v_option_872_;
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_val_873_);
lean_dec(v_option_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_881_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = lean_apply_1(v_f_871_, v_val_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_879_ = v___x_875_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_m_884_, lean_object* v_a_885_, lean_object* v_f_886_){
_start:
{
lean_object* v___f_887_; lean_object* v___x_888_; 
v___f_887_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_887_, 0, v_f_886_);
v___x_888_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098___redArg(v_inst_882_, v_inst_883_, v_m_884_, v_a_885_, v___f_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_m_893_, lean_object* v_a_894_, lean_object* v_f_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify_u2098___redArg(v_inst_891_, v_inst_892_, v_m_893_, v_a_894_, v_f_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(lean_object* v_f_897_, lean_object* v_acc_898_, lean_object* v_a_899_){
_start:
{
if (lean_obj_tag(v_a_899_) == 0)
{
lean_dec_ref(v_f_897_);
return v_acc_898_;
}
else
{
lean_object* v_key_900_; lean_object* v_value_901_; lean_object* v_tail_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v_key_900_ = lean_ctor_get(v_a_899_, 0);
v_value_901_ = lean_ctor_get(v_a_899_, 1);
v_tail_902_ = lean_ctor_get(v_a_899_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_899_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v_a_899_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_tail_902_);
lean_inc(v_value_901_);
lean_inc(v_key_900_);
lean_dec(v_a_899_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; 
lean_inc_ref(v_f_897_);
lean_inc(v_key_900_);
v___x_906_ = lean_apply_2(v_f_897_, v_key_900_, v_value_901_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_del_object(v___x_904_);
lean_dec(v_key_900_);
v_a_899_ = v_tail_902_;
goto _start;
}
else
{
lean_object* v_val_908_; lean_object* v___x_910_; 
v_val_908_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_val_908_);
lean_dec_ref_known(v___x_906_, 1);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 2, v_acc_898_);
lean_ctor_set(v___x_904_, 1, v_val_908_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_key_900_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_val_908_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_acc_898_);
v___x_910_ = v_reuseFailAlloc_912_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v_acc_898_ = v___x_910_;
v_a_899_ = v_tail_902_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0(lean_object* v_f_914_, lean_object* v_l_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_box(0);
v___x_917_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_914_, v___x_916_, v_l_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(lean_object* v_m_918_, lean_object* v_f_919_){
_start:
{
lean_object* v_buckets_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_buckets_920_ = lean_ctor_get(v_m_918_, 1);
lean_inc_ref(v_buckets_920_);
lean_dec_ref(v_m_918_);
v___f_921_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_921_, 0, v_f_919_);
v___x_922_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_920_, v___f_921_);
v___x_923_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098(lean_object* v_00_u03b1_924_, lean_object* v_00_u03b2_925_, lean_object* v_00_u03b4_926_, lean_object* v_m_927_, lean_object* v_f_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap_u2098___redArg(v_m_927_, v_f_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0(lean_object* v_00_u03b1_930_, lean_object* v_00_u03b2_931_, lean_object* v_00_u03b4_932_, lean_object* v_f_933_, lean_object* v_acc_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filterMap_go___at___00Std_DHashMap_Internal_Raw_u2080_filterMap_u2098_spec__0___redArg(v_f_933_, v_acc_934_, v_a_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(lean_object* v_f_937_, lean_object* v_acc_938_, lean_object* v_a_939_){
_start:
{
if (lean_obj_tag(v_a_939_) == 0)
{
lean_dec(v_f_937_);
return v_acc_938_;
}
else
{
lean_object* v_key_940_; lean_object* v_value_941_; lean_object* v_tail_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_951_; 
v_key_940_ = lean_ctor_get(v_a_939_, 0);
v_value_941_ = lean_ctor_get(v_a_939_, 1);
v_tail_942_ = lean_ctor_get(v_a_939_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_944_ = v_a_939_;
v_isShared_945_ = v_isSharedCheck_951_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_tail_942_);
lean_inc(v_value_941_);
lean_inc(v_key_940_);
lean_dec(v_a_939_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_951_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc(v_f_937_);
lean_inc(v_key_940_);
v___x_946_ = lean_apply_2(v_f_937_, v_key_940_, v_value_941_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v_acc_938_);
lean_ctor_set(v___x_944_, 1, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_key_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_acc_938_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
v_acc_938_ = v___x_948_;
v_a_939_ = v_tail_942_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0(lean_object* v_f_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = lean_box(0);
v___x_955_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_952_, v___x_954_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(lean_object* v_m_956_, lean_object* v_f_957_){
_start:
{
lean_object* v_size_958_; lean_object* v_buckets_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_968_; 
v_size_958_ = lean_ctor_get(v_m_956_, 0);
v_buckets_959_ = lean_ctor_get(v_m_956_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_m_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_961_ = v_m_956_;
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_buckets_959_);
lean_inc(v_size_958_);
lean_dec(v_m_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___x_966_; 
v___f_963_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_963_, 0, v_f_957_);
v___x_964_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_959_, v___f_963_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_964_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_size_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map_u2098(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_00_u03b4_971_, lean_object* v_m_972_, lean_object* v_f_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Std_DHashMap_Internal_Raw_u2080_map_u2098___redArg(v_m_972_, v_f_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0(lean_object* v_00_u03b1_975_, lean_object* v_00_u03b2_976_, lean_object* v_00_u03b4_977_, lean_object* v_f_978_, lean_object* v_acc_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map_u2098_spec__0___redArg(v_f_978_, v_acc_979_, v_a_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(lean_object* v_f_982_, lean_object* v_acc_983_, lean_object* v_a_984_){
_start:
{
if (lean_obj_tag(v_a_984_) == 0)
{
lean_dec_ref(v_f_982_);
return v_acc_983_;
}
else
{
lean_object* v_key_985_; lean_object* v_value_986_; lean_object* v_tail_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_998_; 
v_key_985_ = lean_ctor_get(v_a_984_, 0);
v_value_986_ = lean_ctor_get(v_a_984_, 1);
v_tail_987_ = lean_ctor_get(v_a_984_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_998_ == 0)
{
v___x_989_ = v_a_984_;
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_tail_987_);
lean_inc(v_value_986_);
lean_inc(v_key_985_);
lean_dec(v_a_984_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_998_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
lean_inc_ref(v_f_982_);
lean_inc(v_value_986_);
lean_inc(v_key_985_);
v___x_991_ = lean_apply_2(v_f_982_, v_key_985_, v_value_986_);
v___x_992_ = lean_unbox(v___x_991_);
if (v___x_992_ == 0)
{
lean_del_object(v___x_989_);
lean_dec(v_value_986_);
lean_dec(v_key_985_);
v_a_984_ = v_tail_987_;
goto _start;
}
else
{
lean_object* v___x_995_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 2, v_acc_983_);
v___x_995_ = v___x_989_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_key_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_value_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_acc_983_);
v___x_995_ = v_reuseFailAlloc_997_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
v_acc_983_ = v___x_995_;
v_a_984_ = v_tail_987_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0(lean_object* v_f_999_, lean_object* v_l_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_box(0);
v___x_1002_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_999_, v___x_1001_, v_l_1000_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(lean_object* v_m_1003_, lean_object* v_f_1004_){
_start:
{
lean_object* v_buckets_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_buckets_1005_ = lean_ctor_get(v_m_1003_, 1);
lean_inc_ref(v_buckets_1005_);
lean_dec_ref(v_m_1003_);
v___f_1006_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1006_, 0, v_f_1004_);
v___x_1007_ = l_Std_DHashMap_Internal_updateAllBuckets___redArg(v_buckets_1005_, v___f_1006_);
v___x_1008_ = l_Std_DHashMap_Internal_withComputedSize___redArg(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter_u2098(lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_m_1011_, lean_object* v_f_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_1011_, v_f_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_f_1016_, lean_object* v_acc_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter_u2098_spec__0___redArg(v_f_1016_, v_acc_1017_, v_a_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_m_1022_, lean_object* v_l_1023_){
_start:
{
if (lean_obj_tag(v_l_1023_) == 0)
{
lean_dec_ref(v_inst_1021_);
lean_dec_ref(v_inst_1020_);
return v_m_1022_;
}
else
{
lean_object* v_head_1024_; lean_object* v_tail_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___x_1028_; 
v_head_1024_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_head_1024_);
v_tail_1025_ = lean_ctor_get(v_l_1023_, 1);
lean_inc(v_tail_1025_);
lean_dec_ref_known(v_l_1023_, 2);
v_fst_1026_ = lean_ctor_get(v_head_1024_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v_head_1024_, 1);
lean_inc(v_snd_1027_);
lean_dec(v_head_1024_);
lean_inc_ref(v_inst_1021_);
lean_inc_ref(v_inst_1020_);
v___x_1028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1020_, v_inst_1021_, v_m_1022_, v_fst_1026_, v_snd_1027_);
v_m_1022_ = v___x_1028_;
v_l_1023_ = v_tail_1025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_m_1034_, lean_object* v_l_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(v_inst_1032_, v_inst_1033_, v_m_1034_, v_l_1035_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_m_1039_, lean_object* v_l_1040_){
_start:
{
if (lean_obj_tag(v_l_1040_) == 0)
{
lean_dec_ref(v_inst_1038_);
lean_dec_ref(v_inst_1037_);
return v_m_1039_;
}
else
{
lean_object* v_head_1041_; lean_object* v_tail_1042_; lean_object* v___x_1043_; 
v_head_1041_ = lean_ctor_get(v_l_1040_, 0);
lean_inc(v_head_1041_);
v_tail_1042_ = lean_ctor_get(v_l_1040_, 1);
lean_inc(v_tail_1042_);
lean_dec_ref_known(v_l_1040_, 2);
lean_inc_ref(v_inst_1038_);
lean_inc_ref(v_inst_1037_);
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1037_, v_inst_1038_, v_m_1039_, v_head_1041_);
v_m_1039_ = v___x_1043_;
v_l_1040_ = v_tail_1042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_m_1049_, lean_object* v_l_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Std_DHashMap_Internal_Raw_u2080_eraseList_u2098___redArg(v_inst_1047_, v_inst_1048_, v_m_1049_, v_l_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_m_u2082_1054_, uint8_t v___x_1055_, lean_object* v_k_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Std_DHashMap_Internal_Raw_u2080_contains_u2098___redArg(v_inst_1052_, v_inst_1053_, v_m_u2082_1054_, v_k_1056_);
if (v___x_1058_ == 0)
{
return v___x_1055_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = 0;
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed(lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_m_u2082_1062_, lean_object* v___x_1063_, lean_object* v_k_1064_, lean_object* v_x_1065_){
_start:
{
uint8_t v___x_51__boxed_1066_; uint8_t v_res_1067_; lean_object* v_r_1068_; 
v___x_51__boxed_1066_ = lean_unbox(v___x_1063_);
v_res_1067_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0(v_inst_1060_, v_inst_1061_, v_m_u2082_1062_, v___x_51__boxed_1066_, v_k_1064_, v_x_1065_);
lean_dec(v_x_1065_);
lean_dec_ref(v_m_u2082_1062_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_m_u2081_1094_, lean_object* v_m_u2082_1095_){
_start:
{
lean_object* v_size_1096_; lean_object* v_size_1097_; lean_object* v_buckets_1098_; uint8_t v___x_1099_; 
v_size_1096_ = lean_ctor_get(v_m_u2081_1094_, 0);
v_size_1097_ = lean_ctor_get(v_m_u2082_1095_, 0);
v_buckets_1098_ = lean_ctor_get(v_m_u2082_1095_, 1);
v___x_1099_ = lean_nat_dec_le(v_size_1096_, v_size_1097_);
if (v___x_1099_ == 0)
{
lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_inc_ref(v_buckets_1098_);
lean_dec_ref(v_m_u2082_1095_);
v___f_1100_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___closed__11));
v___x_1101_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1098_);
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1100_, v_inst_1092_, v_inst_1093_, v_m_u2081_1094_, v___x_1101_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_box(v___x_1099_);
v___f_1104_ = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1104_, 0, v_inst_1092_);
lean_closure_set(v___f_1104_, 1, v_inst_1093_);
lean_closure_set(v___f_1104_, 2, v_m_u2082_1095_);
lean_closure_set(v___f_1104_, 3, v___x_1103_);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_filter_u2098___redArg(v_m_u2081_1094_, v___f_1104_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_diff_u2098(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_m_u2081_1110_, lean_object* v_m_u2082_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_Raw_u2080_diff_u2098___redArg(v_inst_1108_, v_inst_1109_, v_m_u2081_1110_, v_m_u2082_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_m_1115_, lean_object* v_l_1116_){
_start:
{
if (lean_obj_tag(v_l_1116_) == 0)
{
lean_dec_ref(v_inst_1114_);
lean_dec_ref(v_inst_1113_);
return v_m_1115_;
}
else
{
lean_object* v_head_1117_; lean_object* v_tail_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1121_; 
v_head_1117_ = lean_ctor_get(v_l_1116_, 0);
lean_inc(v_head_1117_);
v_tail_1118_ = lean_ctor_get(v_l_1116_, 1);
lean_inc(v_tail_1118_);
lean_dec_ref_known(v_l_1116_, 2);
v_fst_1119_ = lean_ctor_get(v_head_1117_, 0);
lean_inc(v_fst_1119_);
v_snd_1120_ = lean_ctor_get(v_head_1117_, 1);
lean_inc(v_snd_1120_);
lean_dec(v_head_1117_);
lean_inc_ref(v_inst_1114_);
lean_inc_ref(v_inst_1113_);
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1113_, v_inst_1114_, v_m_1115_, v_fst_1119_, v_snd_1120_);
v_m_1115_ = v___x_1121_;
v_l_1116_ = v_tail_1118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_m_1127_, lean_object* v_l_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1125_, v_inst_1126_, v_m_1127_, v_l_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_m_u2081_1132_, lean_object* v_m_u2082_1133_){
_start:
{
lean_object* v_size_1134_; lean_object* v_buckets_1135_; lean_object* v_size_1136_; lean_object* v_buckets_1137_; uint8_t v___x_1138_; 
v_size_1134_ = lean_ctor_get(v_m_u2081_1132_, 0);
v_buckets_1135_ = lean_ctor_get(v_m_u2081_1132_, 1);
v_size_1136_ = lean_ctor_get(v_m_u2082_1133_, 0);
v_buckets_1137_ = lean_ctor_get(v_m_u2082_1133_, 1);
v___x_1138_ = lean_nat_dec_le(v_size_1134_, v_size_1136_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_inc_ref(v_buckets_1137_);
lean_dec_ref(v_m_u2082_1133_);
v___x_1139_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1137_);
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_insertList_u2098___redArg(v_inst_1130_, v_inst_1131_, v_m_u2081_1132_, v___x_1139_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v_buckets_1135_);
lean_dec_ref(v_m_u2081_1132_);
v___x_1141_ = l_Std_DHashMap_Internal_toListModel___redArg(v_buckets_1135_);
v___x_1142_ = l_Std_DHashMap_Internal_Raw_u2080_insertListIfNew_u2098___redArg(v_inst_1130_, v_inst_1131_, v_m_u2082_1133_, v___x_1141_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_union_u2098(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_m_u2081_1147_, lean_object* v_m_u2082_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_union_u2098___redArg(v_inst_1145_, v_inst_1146_, v_m_u2081_1147_, v_m_u2082_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_m_1152_, lean_object* v_sofar_1153_, lean_object* v_k_1154_){
_start:
{
lean_object* v___x_1155_; 
lean_inc_ref(v_inst_1151_);
lean_inc_ref(v_inst_1150_);
v___x_1155_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f_u2098___redArg(v_inst_1150_, v_inst_1151_, v_m_1152_, v_k_1154_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_inst_1150_);
return v_sofar_1153_;
}
else
{
lean_object* v_val_1156_; lean_object* v_fst_1157_; lean_object* v_snd_1158_; lean_object* v___x_1159_; 
v_val_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_val_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v_fst_1157_ = lean_ctor_get(v_val_1156_, 0);
lean_inc(v_fst_1157_);
v_snd_1158_ = lean_ctor_get(v_val_1156_, 1);
lean_inc(v_snd_1158_);
lean_dec(v_val_1156_);
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_insert_u2098___redArg(v_inst_1150_, v_inst_1151_, v_sofar_1153_, v_fst_1157_, v_snd_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg___boxed(lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_m_1162_, lean_object* v_sofar_1163_, lean_object* v_k_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1160_, v_inst_1161_, v_m_1162_, v_sofar_1163_, v_k_1164_);
lean_dec_ref(v_m_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_m_1170_, lean_object* v_sofar_1171_, lean_object* v_k_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___redArg(v_inst_1168_, v_inst_1169_, v_m_1170_, v_sofar_1171_, v_k_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098___boxed(lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_m_1178_, lean_object* v_sofar_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_DHashMap_Internal_Raw_u2080_interSmallerFn_u2098(v_00_u03b1_1174_, v_00_u03b2_1175_, v_inst_1176_, v_inst_1177_, v_m_1178_, v_sofar_1179_, v_k_1180_);
lean_dec_ref(v_m_1178_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_m_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_buckets_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_buckets_1186_ = lean_ctor_get(v_m_1184_, 1);
lean_inc(v_a_1185_);
v___x_1187_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1183_, v_buckets_1186_, v_a_1185_);
v___x_1188_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_1182_, v_a_1185_, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg___boxed(lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_m_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1189_, v_inst_1190_, v_m_1191_, v_a_1192_);
lean_dec_ref(v_m_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_m_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1196_, v_inst_1197_, v_m_1198_, v_a_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098(v_00_u03b1_1201_, v_00_u03b2_1202_, v_inst_1203_, v_inst_1204_, v_m_1205_, v_a_1206_);
lean_dec_ref(v_m_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(lean_object* v_inst_1208_, lean_object* v_inst_1209_, lean_object* v_m_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_buckets_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_buckets_1212_ = lean_ctor_get(v_m_1210_, 1);
lean_inc(v_a_1211_);
v___x_1213_ = l_Std_DHashMap_Internal_bucket___redArg(v_inst_1209_, v_buckets_1212_, v_a_1211_);
v___x_1214_ = l_Std_DHashMap_Internal_AssocList_get___redArg(v_inst_1208_, v_a_1211_, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg___boxed(lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_m_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_1215_, v_inst_1216_, v_m_1217_, v_a_1218_);
lean_dec_ref(v_m_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_m_1224_, lean_object* v_a_1225_, lean_object* v_h_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___redArg(v_inst_1222_, v_inst_1223_, v_m_1224_, v_a_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_m_1232_, lean_object* v_a_1233_, lean_object* v_h_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_u2098(v_00_u03b1_1228_, v_00_u03b2_1229_, v_inst_1230_, v_inst_1231_, v_m_1232_, v_a_1233_, v_h_1234_);
lean_dec_ref(v_m_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_fallback_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1236_, v_inst_1237_, v_m_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_inc(v_fallback_1240_);
return v_fallback_1240_;
}
else
{
lean_object* v_val_1242_; 
v_val_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v___x_1241_, 1);
return v_val_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg___boxed(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_fallback_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_1243_, v_inst_1244_, v_m_1245_, v_a_1246_, v_fallback_1247_);
lean_dec(v_fallback_1247_);
lean_dec_ref(v_m_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(lean_object* v_00_u03b1_1249_, lean_object* v_00_u03b2_1250_, lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_m_1253_, lean_object* v_a_1254_, lean_object* v_fallback_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___redArg(v_inst_1251_, v_inst_1252_, v_m_1253_, v_a_1254_, v_fallback_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_m_1261_, lean_object* v_a_1262_, lean_object* v_fallback_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD_u2098(v_00_u03b1_1257_, v_00_u03b2_1258_, v_inst_1259_, v_inst_1260_, v_m_1261_, v_a_1262_, v_fallback_1263_);
lean_dec(v_fallback_1263_);
lean_dec_ref(v_m_1261_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_m_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f_u2098___redArg(v_inst_1265_, v_inst_1266_, v_m_1268_, v_a_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_get_x21_u2098___redArg___closed__3);
v___x_1272_ = l_panic___redArg(v_inst_1267_, v___x_1271_);
return v___x_1272_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1270_, 1);
return v_val_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg___boxed(lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_m_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_1274_, v_inst_1275_, v_inst_1276_, v_m_1277_, v_a_1278_);
lean_dec_ref(v_m_1277_);
lean_dec(v_inst_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_m_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___redArg(v_inst_1282_, v_inst_1283_, v_inst_1284_, v_m_1285_, v_a_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_00_u03b2_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_m_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21_u2098(v_00_u03b1_1288_, v_00_u03b2_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v_m_1293_, v_a_1294_);
lean_dec_ref(v_m_1293_);
lean_dec(v_inst_1292_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_m_1298_, lean_object* v_l_1299_){
_start:
{
if (lean_obj_tag(v_l_1299_) == 0)
{
lean_dec_ref(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
return v_m_1298_;
}
else
{
lean_object* v_head_1300_; lean_object* v_tail_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1304_; 
v_head_1300_ = lean_ctor_get(v_l_1299_, 0);
lean_inc(v_head_1300_);
v_tail_1301_ = lean_ctor_get(v_l_1299_, 1);
lean_inc(v_tail_1301_);
lean_dec_ref_known(v_l_1299_, 2);
v_fst_1302_ = lean_ctor_get(v_head_1300_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v_head_1300_, 1);
lean_inc(v_snd_1303_);
lean_dec(v_head_1300_);
lean_inc_ref(v_inst_1297_);
lean_inc_ref(v_inst_1296_);
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1296_, v_inst_1297_, v_m_1298_, v_fst_1302_, v_snd_1303_);
v_m_1298_ = v___x_1304_;
v_l_1299_ = v_tail_1301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098(lean_object* v_00_u03b1_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_m_1310_, lean_object* v_l_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098___redArg(v_inst_1308_, v_inst_1309_, v_m_1310_, v_l_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_m_1315_, lean_object* v_l_1316_){
_start:
{
if (lean_obj_tag(v_l_1316_) == 0)
{
lean_dec_ref(v_inst_1314_);
lean_dec_ref(v_inst_1313_);
return v_m_1315_;
}
else
{
lean_object* v_head_1317_; lean_object* v_tail_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_head_1317_ = lean_ctor_get(v_l_1316_, 0);
lean_inc(v_head_1317_);
v_tail_1318_ = lean_ctor_get(v_l_1316_, 1);
lean_inc(v_tail_1318_);
lean_dec_ref_known(v_l_1316_, 2);
v___x_1319_ = lean_box(0);
lean_inc_ref(v_inst_1314_);
lean_inc_ref(v_inst_1313_);
v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1313_, v_inst_1314_, v_m_1315_, v_head_1317_, v___x_1319_);
v_m_1315_ = v___x_1320_;
v_l_1316_ = v_tail_1318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098(lean_object* v_00_u03b1_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_m_1325_, lean_object* v_l_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertListIfNewUnit_u2098___redArg(v_inst_1323_, v_inst_1324_, v_m_1325_, v_l_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter___redArg(lean_object* v_m_1328_, lean_object* v_h__1_1329_){
_start:
{
lean_object* v_size_1330_; lean_object* v_buckets_1331_; lean_object* v___x_1332_; 
v_size_1330_ = lean_ctor_get(v_m_1328_, 0);
lean_inc(v_size_1330_);
v_buckets_1331_ = lean_ctor_get(v_m_1328_, 1);
lean_inc_ref(v_buckets_1331_);
lean_dec_ref(v_m_1328_);
v___x_1332_ = lean_apply_3(v_h__1_1329_, v_size_1330_, v_buckets_1331_, lean_box(0));
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_expandIfNecessary_match__1_splitter(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_motive_1335_, lean_object* v_m_1336_, lean_object* v_h__1_1337_){
_start:
{
lean_object* v_size_1338_; lean_object* v_buckets_1339_; lean_object* v___x_1340_; 
v_size_1338_ = lean_ctor_get(v_m_1336_, 0);
lean_inc(v_size_1338_);
v_buckets_1339_ = lean_ctor_get(v_m_1336_, 1);
lean_inc_ref(v_buckets_1339_);
lean_dec_ref(v_m_1336_);
v___x_1340_ = lean_apply_3(v_h__1_1337_, v_size_1338_, v_buckets_1339_, lean_box(0));
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___redArg(lean_object* v_x_1341_, lean_object* v_h__1_1342_, lean_object* v_h__2_1343_){
_start:
{
if (lean_obj_tag(v_x_1341_) == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec(v_h__2_1343_);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_apply_1(v_h__1_1342_, v___x_1344_);
return v___x_1345_;
}
else
{
lean_object* v_val_1346_; lean_object* v___x_1347_; 
lean_dec(v_h__1_1342_);
v_val_1346_ = lean_ctor_get(v_x_1341_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v_x_1341_, 1);
v___x_1347_ = lean_apply_1(v_h__2_1343_, v_val_1346_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_a_1350_, lean_object* v_motive_1351_, lean_object* v_x_1352_, lean_object* v_h__1_1353_, lean_object* v_h__2_1354_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec(v_h__2_1354_);
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_apply_1(v_h__1_1353_, v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1358_; 
lean_dec(v_h__1_1353_);
v_val_1357_ = lean_ctor_get(v_x_1352_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v_x_1352_, 1);
v___x_1358_ = lean_apply_1(v_h__2_1354_, v_val_1357_);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter___boxed(lean_object* v_00_u03b1_1359_, lean_object* v_00_u03b2_1360_, lean_object* v_a_1361_, lean_object* v_motive_1362_, lean_object* v_x_1363_, lean_object* v_h__1_1364_, lean_object* v_h__2_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_match__1_splitter(v_00_u03b1_1359_, v_00_u03b2_1360_, v_a_1361_, v_motive_1362_, v_x_1363_, v_h__1_1364_, v_h__2_1365_);
lean_dec(v_a_1361_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___redArg(lean_object* v_x_1367_, lean_object* v_h__1_1368_, lean_object* v_h__2_1369_){
_start:
{
if (lean_obj_tag(v_x_1367_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v_h__2_1369_);
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_apply_1(v_h__1_1368_, v___x_1370_);
return v___x_1371_;
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1373_; 
lean_dec(v_h__1_1368_);
v_val_1372_ = lean_ctor_get(v_x_1367_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_x_1367_, 1);
v___x_1373_ = lean_apply_1(v_h__2_1369_, v_val_1372_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(lean_object* v_00_u03b1_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_a_1376_, lean_object* v_motive_1377_, lean_object* v_x_1378_, lean_object* v_h__1_1379_, lean_object* v_h__2_1380_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
lean_dec(v_h__2_1380_);
v___x_1381_ = lean_box(0);
v___x_1382_ = lean_apply_1(v_h__1_1379_, v___x_1381_);
return v___x_1382_;
}
else
{
lean_object* v_val_1383_; lean_object* v___x_1384_; 
lean_dec(v_h__1_1379_);
v_val_1383_ = lean_ctor_get(v_x_1378_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_x_1378_, 1);
v___x_1384_ = lean_apply_1(v_h__2_1380_, v_val_1383_);
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_a_1387_, lean_object* v_motive_1388_, lean_object* v_x_1389_, lean_object* v_h__1_1390_, lean_object* v_h__2_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_alter_u2098_match__1_splitter(v_00_u03b1_1385_, v_00_u03b2_1386_, v_a_1387_, v_motive_1388_, v_x_1389_, v_h__1_1390_, v_h__2_1391_);
lean_dec(v_a_1387_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(size_t v_x_1393_, lean_object* v_h__1_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_box_usize(v_x_1393_);
v___x_1396_ = lean_apply_2(v_h__1_1394_, v___x_1395_, lean_box(0));
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg___boxed(lean_object* v_x_1397_, lean_object* v_h__1_1398_){
_start:
{
size_t v_x_14__boxed_1399_; lean_object* v_res_1400_; 
v_x_14__boxed_1399_ = lean_unbox_usize(v_x_1397_);
lean_dec(v_x_1397_);
v_res_1400_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___redArg(v_x_14__boxed_1399_, v_h__1_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_data_1403_, lean_object* v_motive_1404_, size_t v_x_1405_, lean_object* v_h__1_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_box_usize(v_x_1405_);
v___x_1408_ = lean_apply_2(v_h__1_1406_, v___x_1407_, lean_box(0));
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_data_1411_, lean_object* v_motive_1412_, lean_object* v_x_1413_, lean_object* v_h__1_1414_){
_start:
{
size_t v_x_21__boxed_1415_; lean_object* v_res_1416_; 
v_x_21__boxed_1415_ = lean_unbox_usize(v_x_1413_);
lean_dec(v_x_1413_);
v_res_1416_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_reinsertAux_match__1_splitter(v_00_u03b1_1409_, v_00_u03b2_1410_, v_data_1411_, v_motive_1412_, v_x_21__boxed_1415_, v_h__1_1414_);
lean_dec_ref(v_data_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter___redArg(lean_object* v_m_1417_, lean_object* v_h__1_1418_){
_start:
{
lean_object* v_size_1419_; lean_object* v_buckets_1420_; lean_object* v___x_1421_; 
v_size_1419_ = lean_ctor_get(v_m_1417_, 0);
lean_inc(v_size_1419_);
v_buckets_1420_ = lean_ctor_get(v_m_1417_, 1);
lean_inc_ref(v_buckets_1420_);
lean_dec_ref(v_m_1417_);
v___x_1421_ = lean_apply_3(v_h__1_1418_, v_size_1419_, v_buckets_1420_, lean_box(0));
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__3_splitter(lean_object* v_00_u03b1_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_motive_1424_, lean_object* v_m_1425_, lean_object* v_h__1_1426_){
_start:
{
lean_object* v_size_1427_; lean_object* v_buckets_1428_; lean_object* v___x_1429_; 
v_size_1427_ = lean_ctor_get(v_m_1425_, 0);
lean_inc(v_size_1427_);
v_buckets_1428_ = lean_ctor_get(v_m_1425_, 1);
lean_inc_ref(v_buckets_1428_);
lean_dec_ref(v_m_1425_);
v___x_1429_ = lean_apply_3(v_h__1_1426_, v_size_1427_, v_buckets_1428_, lean_box(0));
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter___redArg(lean_object* v_x_1430_, lean_object* v_h__1_1431_, lean_object* v_h__2_1432_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_h__2_1432_);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_apply_1(v_h__1_1431_, v___x_1433_);
return v___x_1434_;
}
else
{
lean_object* v_val_1435_; lean_object* v___x_1436_; 
lean_dec(v_h__1_1431_);
v_val_1435_ = lean_ctor_get(v_x_1430_, 0);
lean_inc(v_val_1435_);
lean_dec_ref_known(v_x_1430_, 1);
v___x_1436_ = lean_apply_1(v_h__2_1432_, v_val_1435_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_match__1_splitter(lean_object* v_00_u03b2_1437_, lean_object* v_motive_1438_, lean_object* v_x_1439_, lean_object* v_h__1_1440_, lean_object* v_h__2_1441_){
_start:
{
if (lean_obj_tag(v_x_1439_) == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec(v_h__2_1441_);
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_apply_1(v_h__1_1440_, v___x_1442_);
return v___x_1443_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1445_; 
lean_dec(v_h__1_1440_);
v_val_1444_ = lean_ctor_get(v_x_1439_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v_x_1439_, 1);
v___x_1445_ = lean_apply_1(v_h__2_1441_, v_val_1444_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter___redArg(lean_object* v_x_1446_, lean_object* v_h__1_1447_, lean_object* v_h__2_1448_){
_start:
{
if (lean_obj_tag(v_x_1446_) == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_h__2_1448_);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_apply_1(v_h__1_1447_, v___x_1449_);
return v___x_1450_;
}
else
{
lean_object* v_val_1451_; lean_object* v___x_1452_; 
lean_dec(v_h__1_1447_);
v_val_1451_ = lean_ctor_get(v_x_1446_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v_x_1446_, 1);
v___x_1452_ = lean_apply_1(v_h__2_1448_, v_val_1451_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_alter_u2098_match__1_splitter(lean_object* v_00_u03b2_1453_, lean_object* v_motive_1454_, lean_object* v_x_1455_, lean_object* v_h__1_1456_, lean_object* v_h__2_1457_){
_start:
{
if (lean_obj_tag(v_x_1455_) == 0)
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec(v_h__2_1457_);
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_apply_1(v_h__1_1456_, v___x_1458_);
return v___x_1459_;
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1461_; 
lean_dec(v_h__1_1456_);
v_val_1460_ = lean_ctor_get(v_x_1455_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v_x_1455_, 1);
v___x_1461_ = lean_apply_1(v_h__2_1457_, v_val_1460_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(size_t v_x_1462_, lean_object* v_h__1_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_box_usize(v_x_1462_);
v___x_1465_ = lean_apply_2(v_h__1_1463_, v___x_1464_, lean_box(0));
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg___boxed(lean_object* v_x_1466_, lean_object* v_h__1_1467_){
_start:
{
size_t v_x_14__boxed_1468_; lean_object* v_res_1469_; 
v_x_14__boxed_1468_ = lean_unbox_usize(v_x_1466_);
lean_dec(v_x_1466_);
v_res_1469_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___redArg(v_x_14__boxed_1468_, v_h__1_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(lean_object* v_00_u03b1_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_buckets_1472_, lean_object* v_motive_1473_, size_t v_x_1474_, lean_object* v_h__1_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = lean_box_usize(v_x_1474_);
v___x_1477_ = lean_apply_2(v_h__1_1475_, v___x_1476_, lean_box(0));
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_00_u03b2_1479_, lean_object* v_buckets_1480_, lean_object* v_motive_1481_, lean_object* v_x_1482_, lean_object* v_h__1_1483_){
_start:
{
size_t v_x_21__boxed_1484_; lean_object* v_res_1485_; 
v_x_21__boxed_1484_ = lean_unbox_usize(v_x_1482_);
lean_dec(v_x_1482_);
v_res_1485_ = l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_modify_match__1_splitter(v_00_u03b1_1478_, v_00_u03b2_1479_, v_buckets_1480_, v_motive_1481_, v_x_21__boxed_1484_, v_h__1_1483_);
lean_dec_ref(v_buckets_1480_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter___redArg(lean_object* v_l_1486_, lean_object* v_h__1_1487_, lean_object* v_h__2_1488_){
_start:
{
if (lean_obj_tag(v_l_1486_) == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec(v_h__2_1488_);
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_apply_1(v_h__1_1487_, v___x_1489_);
return v___x_1490_;
}
else
{
lean_object* v_head_1491_; lean_object* v_tail_1492_; lean_object* v___x_1493_; 
lean_dec(v_h__1_1487_);
v_head_1491_ = lean_ctor_get(v_l_1486_, 0);
lean_inc(v_head_1491_);
v_tail_1492_ = lean_ctor_get(v_l_1486_, 1);
lean_inc(v_tail_1492_);
lean_dec_ref_known(v_l_1486_, 2);
v___x_1493_ = lean_apply_2(v_h__2_1488_, v_head_1491_, v_tail_1492_);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_insertList_u2098_match__1_splitter(lean_object* v_00_u03b1_1494_, lean_object* v_00_u03b2_1495_, lean_object* v_motive_1496_, lean_object* v_l_1497_, lean_object* v_h__1_1498_, lean_object* v_h__2_1499_){
_start:
{
if (lean_obj_tag(v_l_1497_) == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_h__2_1499_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_apply_1(v_h__1_1498_, v___x_1500_);
return v___x_1501_;
}
else
{
lean_object* v_head_1502_; lean_object* v_tail_1503_; lean_object* v___x_1504_; 
lean_dec(v_h__1_1498_);
v_head_1502_ = lean_ctor_get(v_l_1497_, 0);
lean_inc(v_head_1502_);
v_tail_1503_ = lean_ctor_get(v_l_1497_, 1);
lean_inc(v_tail_1503_);
lean_dec_ref_known(v_l_1497_, 2);
v___x_1504_ = lean_apply_2(v_h__2_1499_, v_head_1502_, v_tail_1503_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter___redArg(lean_object* v_l_1505_, lean_object* v_h__1_1506_, lean_object* v_h__2_1507_){
_start:
{
if (lean_obj_tag(v_l_1505_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_h__2_1507_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_apply_1(v_h__1_1506_, v___x_1508_);
return v___x_1509_;
}
else
{
lean_object* v_head_1510_; lean_object* v_tail_1511_; lean_object* v___x_1512_; 
lean_dec(v_h__1_1506_);
v_head_1510_ = lean_ctor_get(v_l_1505_, 0);
lean_inc(v_head_1510_);
v_tail_1511_ = lean_ctor_get(v_l_1505_, 1);
lean_inc(v_tail_1511_);
lean_dec_ref_known(v_l_1505_, 2);
v___x_1512_ = lean_apply_2(v_h__2_1507_, v_head_1510_, v_tail_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_eraseList_u2098_match__1_splitter(lean_object* v_00_u03b1_1513_, lean_object* v_motive_1514_, lean_object* v_l_1515_, lean_object* v_h__1_1516_, lean_object* v_h__2_1517_){
_start:
{
if (lean_obj_tag(v_l_1515_) == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_h__2_1517_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_apply_1(v_h__1_1516_, v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v_head_1520_; lean_object* v_tail_1521_; lean_object* v___x_1522_; 
lean_dec(v_h__1_1516_);
v_head_1520_ = lean_ctor_get(v_l_1515_, 0);
lean_inc(v_head_1520_);
v_tail_1521_ = lean_ctor_get(v_l_1515_, 1);
lean_inc(v_tail_1521_);
lean_dec_ref_known(v_l_1515_, 2);
v___x_1522_ = lean_apply_2(v_h__2_1517_, v_head_1520_, v_tail_1521_);
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter___redArg(lean_object* v_l_1523_, lean_object* v_h__1_1524_, lean_object* v_h__2_1525_){
_start:
{
if (lean_obj_tag(v_l_1523_) == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v_h__2_1525_);
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_apply_1(v_h__1_1524_, v___x_1526_);
return v___x_1527_;
}
else
{
lean_object* v_head_1528_; lean_object* v_tail_1529_; lean_object* v___x_1530_; 
lean_dec(v_h__1_1524_);
v_head_1528_ = lean_ctor_get(v_l_1523_, 0);
lean_inc(v_head_1528_);
v_tail_1529_ = lean_ctor_get(v_l_1523_, 1);
lean_inc(v_tail_1529_);
lean_dec_ref_known(v_l_1523_, 2);
v___x_1530_ = lean_apply_2(v_h__2_1525_, v_head_1528_, v_tail_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Model_0__Std_DHashMap_Internal_Raw_u2080_Const_insertList_u2098_match__1_splitter(lean_object* v_00_u03b1_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_motive_1533_, lean_object* v_l_1534_, lean_object* v_h__1_1535_, lean_object* v_h__2_1536_){
_start:
{
if (lean_obj_tag(v_l_1534_) == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_h__2_1536_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_apply_1(v_h__1_1535_, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v_head_1539_; lean_object* v_tail_1540_; lean_object* v___x_1541_; 
lean_dec(v_h__1_1535_);
v_head_1539_ = lean_ctor_get(v_l_1534_, 0);
lean_inc(v_head_1539_);
v_tail_1540_ = lean_ctor_get(v_l_1534_, 1);
lean_inc(v_tail_1540_);
lean_dec_ref_known(v_l_1534_, 2);
v___x_1541_ = lean_apply_2(v_h__2_1536_, v_head_1539_, v_tail_1540_);
return v___x_1541_;
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
