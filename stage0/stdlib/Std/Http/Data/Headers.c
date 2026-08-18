// Lean compiler output
// Module: Std.Http.Data.Headers
// Imports: public import Std.Http.Data.Headers.Basic public import Std.Http.Data.Headers.Name public import Std.Http.Data.Headers.Value
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Http_Header_instReprName_repr___redArg(lean_object*);
lean_object* l_Std_Http_Header_instReprValue_repr___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_Http_Header_instBEqValue_beq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Name_ofString_x3f(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x3f(lean_object*);
static const lean_array_object l_Std_Http_instInhabitedHeaders_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_instInhabitedHeaders_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedHeaders_default___closed__0_value;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__1;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__2;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__3;
static lean_once_cell_t l_Std_Http_instInhabitedHeaders_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedHeaders_default___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedHeaders;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__0 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__0_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__1 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__2 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__4 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__5;
static lean_once_cell_t l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__7 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__8 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__8_value;
static const lean_string_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__9 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__10 = (const lean_object*)&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9(lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7_spec__11_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__3;
static lean_once_cell_t l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__4;
static const lean_ctor_object l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__5 = (const lean_object*)&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__3_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indexes"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__10_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "validity"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__12_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__14_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__16_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Std_Http_instReprHeaders_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_instReprHeaders_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_instReprHeaders_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_instReprHeaders_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instReprHeaders_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instReprHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instReprHeaders_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instReprHeaders___closed__0 = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_instReprHeaders = (const lean_object*)&l_Std_Http_instReprHeaders___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_instMembershipNameHeaders;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__0 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__0_value;
static const lean_closure_object l_Std_Http_instDecidableMemNameHeaders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instDecidableMemNameHeaders___closed__1 = (const lean_object*)&l_Std_Http_instDecidableMemNameHeaders___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__0 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__1 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__2 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__3 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__4 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__5 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value;
static const lean_closure_object l_Std_Http_Headers_getAll___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__6 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__0_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__7 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__7_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__2_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__3_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__4_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__8 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Headers_getAll___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__8_value),((lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_Headers_getAll___redArg___closed__9 = (const lean_object*)&l_Std_Http_Headers_getAll___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Headers_hasEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Headers_hasEntry___closed__0 = (const lean_object*)&l_Std_Http_Headers_hasEntry___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Headers_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Headers_get_x21___closed__0 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__0_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__1 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__1_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__2 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__2_value;
static const lean_string_object l_Std_Http_Headers_get_x21___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Http_Headers_get_x21___closed__3 = (const lean_object*)&l_Std_Http_Headers_get_x21___closed__3_value;
static lean_once_cell_t l_Std_Http_Headers_get_x21___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_get_x21___closed__4;
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object*);
static lean_once_cell_t l_Std_Http_Headers_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_empty___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Headers_empty;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__2___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Headers_erase___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_erase___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instToString___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Headers_instToString___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Headers_instToString___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__1___closed__2_value;
static lean_once_cell_t l_Std_Http_Headers_instToString___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_instToString___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object*);
static const lean_string_object l_Std_Http_Headers_instToString___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Headers_instToString___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instToString___closed__0 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instToString___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instToString___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instToString___closed__1 = (const lean_object*)&l_Std_Http_Headers_instToString___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instToString = (const lean_object*)&l_Std_Http_Headers_instToString___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instEncodeV11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instEncodeV11___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__0_value)} };
static const lean_object* l_Std_Http_Headers_instEncodeV11___closed__1 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instEncodeV11 = (const lean_object*)&l_Std_Http_Headers_instEncodeV11___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEmptyCollection;
static lean_once_cell_t l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0;
static lean_once_cell_t l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object*);
static const lean_closure_object l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instSingletonProdNameValue___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instSingletonProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instSingletonProdNameValue = (const lean_object*)&l_Std_Http_Headers_instSingletonProdNameValue___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Headers_instInsertProdNameValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_instInsertProdNameValue___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instInsertProdNameValue___closed__0 = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instInsertProdNameValue = (const lean_object*)&l_Std_Http_Headers_instInsertProdNameValue___closed__0_value;
static const lean_closure_object l_Std_Http_Headers_instUnion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Headers_merge___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Headers_instUnion___closed__0 = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Headers_instUnion = (const lean_object*)&l_Std_Http_Headers_instUnion___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object*, lean_object*);
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__2(void){
_start:
{
lean_object* v_cellCount_5_; lean_object* v___x_6_; 
v_cellCount_5_ = lean_unsigned_to_nat(16u);
v___x_6_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__2, &l_Std_Http_instInhabitedHeaders_default___closed__2_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__2);
v___x_8_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__1, &l_Std_Http_instInhabitedHeaders_default___closed__1_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__1);
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__3, &l_Std_Http_instInhabitedHeaders_default___closed__3_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__3);
v___x_12_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders_default(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__4, &l_Std_Http_instInhabitedHeaders_default___closed__4_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__4);
return v___x_14_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedHeaders(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_instReprHeaders_repr_spec__1(lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_nat_to_int(v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__6(lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_dec(v_x_18_);
return v_x_19_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_31_; 
v_head_21_ = lean_ctor_get(v_x_20_, 0);
v_tail_22_ = lean_ctor_get(v_x_20_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_31_ == 0)
{
v___x_24_ = v_x_20_;
v_isShared_25_ = v_isSharedCheck_31_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_tail_22_);
lean_inc(v_head_21_);
lean_dec(v_x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_31_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
lean_inc(v_x_18_);
if (v_isShared_25_ == 0)
{
lean_ctor_set_tag(v___x_24_, 5);
lean_ctor_set(v___x_24_, 1, v_x_18_);
lean_ctor_set(v___x_24_, 0, v_x_19_);
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_x_19_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_x_18_);
v___x_27_ = v_reuseFailAlloc_30_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_head_21_);
v_x_19_ = v___x_28_;
v_x_20_ = v_tail_22_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_34_; 
lean_dec(v_x_33_);
v___x_34_ = lean_box(0);
return v___x_34_;
}
else
{
lean_object* v_tail_35_; 
v_tail_35_ = lean_ctor_get(v_x_32_, 1);
if (lean_obj_tag(v_tail_35_) == 0)
{
lean_object* v_head_36_; 
lean_dec(v_x_33_);
v_head_36_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_36_);
lean_dec_ref_known(v_x_32_, 2);
return v_head_36_;
}
else
{
lean_object* v_head_37_; lean_object* v___x_38_; 
lean_inc(v_tail_35_);
v_head_37_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_head_37_);
lean_dec_ref_known(v_x_32_, 2);
v___x_38_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3_spec__6(v_x_33_, v_head_37_, v_tail_35_);
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_dec(v_x_39_);
return v_x_40_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_54_; 
v_head_42_ = lean_ctor_get(v_x_41_, 0);
v_tail_43_ = lean_ctor_get(v_x_41_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_54_ == 0)
{
v___x_45_ = v_x_41_;
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_tail_43_);
lean_inc(v_head_42_);
lean_dec(v_x_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
lean_inc(v_x_39_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 5);
lean_ctor_set(v___x_45_, 1, v_x_39_);
lean_ctor_set(v___x_45_, 0, v_x_40_);
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_x_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_x_39_);
v___x_48_ = v_reuseFailAlloc_53_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = l_Nat_reprFast(v_head_42_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
v___x_51_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_48_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v_x_40_ = v___x_51_;
v_x_41_ = v_tail_43_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12_spec__14(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_dec(v_x_55_);
return v_x_56_;
}
else
{
lean_object* v_head_58_; lean_object* v_tail_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_70_; 
v_head_58_ = lean_ctor_get(v_x_57_, 0);
v_tail_59_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_70_ == 0)
{
v___x_61_ = v_x_57_;
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_tail_59_);
lean_inc(v_head_58_);
lean_dec(v_x_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_64_; 
lean_inc(v_x_55_);
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 5);
lean_ctor_set(v___x_61_, 1, v_x_55_);
lean_ctor_set(v___x_61_, 0, v_x_56_);
v___x_64_ = v___x_61_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_x_56_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_x_55_);
v___x_64_ = v_reuseFailAlloc_69_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = l_Nat_reprFast(v_head_58_);
v___x_66_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12_spec__14_spec__16(v_x_55_, v___x_67_, v_tail_59_);
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12___lam__0(lean_object* v___y_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = l_Nat_reprFast(v___y_71_);
v___x_73_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v___x_76_; 
lean_dec(v_x_75_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v_tail_77_; 
v_tail_77_ = lean_ctor_get(v_x_74_, 1);
if (lean_obj_tag(v_tail_77_) == 0)
{
lean_object* v_head_78_; lean_object* v___x_79_; 
lean_dec(v_x_75_);
v_head_78_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_head_78_);
lean_dec_ref_known(v_x_74_, 2);
v___x_79_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12___lam__0(v_head_78_);
return v___x_79_;
}
else
{
lean_object* v_head_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_inc(v_tail_77_);
v_head_80_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_head_80_);
lean_dec_ref_known(v_x_74_, 2);
v___x_81_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12___lam__0(v_head_80_);
v___x_82_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12_spec__14(v_x_75_, v___x_81_, v_tail_77_);
return v___x_82_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__5(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__0));
v___x_92_ = lean_string_length(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__5, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__5_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__5);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9(lean_object* v_xs_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_103_ = lean_array_get_size(v_xs_102_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_106_ = lean_array_to_list(v_xs_102_);
v___x_107_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3));
v___x_108_ = l_Std_Format_joinSep___at___00Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9_spec__12(v___x_106_, v___x_107_);
v___x_109_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6);
v___x_110_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__7));
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_108_);
v___x_112_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__8));
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_109_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = l_Std_Format_fill(v___x_114_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
lean_dec_ref(v_xs_102_);
v___x_116_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__10));
return v___x_116_;
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__0));
v___x_120_ = lean_string_length(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__2);
v___x_122_ = lean_nat_to_int(v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(lean_object* v_x_127_){
_start:
{
lean_object* v_fst_128_; lean_object* v_snd_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_151_; 
v_fst_128_ = lean_ctor_get(v_x_127_, 0);
v_snd_129_ = lean_ctor_get(v_x_127_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_151_ == 0)
{
v___x_131_ = v_x_127_;
v_isShared_132_ = v_isSharedCheck_151_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_snd_129_);
lean_inc(v_fst_128_);
lean_dec(v_x_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_151_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_128_);
v___x_134_ = lean_box(0);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 1);
lean_ctor_set(v___x_131_, 1, v___x_134_);
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_150_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; 
v___x_137_ = l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9(v_snd_129_);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
v___x_139_ = l_List_reverse___redArg(v___x_138_);
v___x_140_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3));
v___x_141_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_139_, v___x_140_);
v___x_142_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3);
v___x_143_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__4));
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_141_);
v___x_145_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__5));
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_142_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7_spec__11_spec__15(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_dec(v_x_152_);
return v_x_153_;
}
else
{
lean_object* v_head_155_; lean_object* v_tail_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_166_; 
v_head_155_ = lean_ctor_get(v_x_154_, 0);
v_tail_156_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_166_ == 0)
{
v___x_158_ = v_x_154_;
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_tail_156_);
lean_inc(v_head_155_);
lean_dec(v_x_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_166_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
lean_inc(v_x_152_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 5);
lean_ctor_set(v___x_158_, 1, v_x_152_);
lean_ctor_set(v___x_158_, 0, v_x_153_);
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_x_153_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_x_152_);
v___x_161_ = v_reuseFailAlloc_165_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(v_head_155_);
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v_x_153_ = v___x_163_;
v_x_154_ = v_tail_156_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7_spec__11(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_dec(v_x_167_);
return v_x_168_;
}
else
{
lean_object* v_head_170_; lean_object* v_tail_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_181_; 
v_head_170_ = lean_ctor_get(v_x_169_, 0);
v_tail_171_ = lean_ctor_get(v_x_169_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_181_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_tail_171_);
lean_inc(v_head_170_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
lean_inc(v_x_167_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 5);
lean_ctor_set(v___x_173_, 1, v_x_167_);
lean_ctor_set(v___x_173_, 0, v_x_168_);
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_x_168_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_x_167_);
v___x_176_ = v_reuseFailAlloc_180_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(v_head_170_);
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7_spec__11_spec__15(v_x_167_, v___x_178_, v_tail_171_);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_182_) == 0)
{
lean_object* v___x_184_; 
lean_dec(v_x_183_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v_tail_185_; 
v_tail_185_ = lean_ctor_get(v_x_182_, 1);
if (lean_obj_tag(v_tail_185_) == 0)
{
lean_object* v_head_186_; lean_object* v___x_187_; 
lean_dec(v_x_183_);
v_head_186_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_head_186_);
lean_dec_ref_known(v_x_182_, 2);
v___x_187_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(v_head_186_);
return v___x_187_;
}
else
{
lean_object* v_head_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_inc(v_tail_185_);
v_head_188_ = lean_ctor_get(v_x_182_, 0);
lean_inc(v_head_188_);
lean_dec_ref_known(v_x_182_, 2);
v___x_189_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(v_head_188_);
v___x_190_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7_spec__11(v_x_183_, v___x_189_, v_tail_185_);
return v___x_190_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__2));
v___x_196_ = lean_string_length(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__3, &l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__3_once, _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__3);
v___x_198_ = lean_nat_to_int(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg(lean_object* v_a_201_){
_start:
{
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__1));
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; 
v___x_203_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3));
v___x_204_ = l_Std_Format_joinSep___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__7(v_a_201_, v___x_203_);
v___x_205_ = lean_obj_once(&l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__4, &l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__4_once, _init_l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__4);
v___x_206_ = ((lean_object*)(l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg___closed__5));
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_204_);
v___x_208_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__8));
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_205_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = 0;
v___x_212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_211_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(lean_object* v_x_213_){
_start:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_237_; 
v_fst_214_ = lean_ctor_get(v_x_213_, 0);
v_snd_215_ = lean_ctor_get(v_x_213_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_237_ == 0)
{
v___x_217_ = v_x_213_;
v_isShared_218_ = v_isSharedCheck_237_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snd_215_);
lean_inc(v_fst_214_);
lean_dec(v_x_213_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_237_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_219_ = l_Std_Http_Header_instReprName_repr___redArg(v_fst_214_);
v___x_220_ = lean_box(0);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 1);
lean_ctor_set(v___x_217_, 1, v___x_220_);
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_236_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v___x_223_ = l_Std_Http_Header_instReprValue_repr___redArg(v_snd_215_);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
v___x_225_ = l_List_reverse___redArg(v___x_224_);
v___x_226_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3));
v___x_227_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2_spec__3(v___x_225_, v___x_226_);
v___x_228_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__3);
v___x_229_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__4));
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_227_);
v___x_231_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg___closed__5));
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_228_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = 0;
v___x_235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__9(lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_dec(v_x_238_);
return v_x_239_;
}
else
{
lean_object* v_head_241_; lean_object* v_tail_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
v_head_241_ = lean_ctor_get(v_x_240_, 0);
v_tail_242_ = lean_ctor_get(v_x_240_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_252_ == 0)
{
v___x_244_ = v_x_240_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_tail_242_);
lean_inc(v_head_241_);
lean_dec(v_x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
lean_inc(v_x_238_);
if (v_isShared_245_ == 0)
{
lean_ctor_set_tag(v___x_244_, 5);
lean_ctor_set(v___x_244_, 1, v_x_238_);
lean_ctor_set(v___x_244_, 0, v_x_239_);
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_x_239_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_x_238_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_241_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v_x_239_ = v___x_249_;
v_x_240_ = v_tail_242_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(lean_object* v_x_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_dec(v_x_253_);
return v_x_254_;
}
else
{
lean_object* v_head_256_; lean_object* v_tail_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_267_; 
v_head_256_ = lean_ctor_get(v_x_255_, 0);
v_tail_257_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_267_ == 0)
{
v___x_259_ = v_x_255_;
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_tail_257_);
lean_inc(v_head_256_);
lean_dec(v_x_255_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
lean_inc(v_x_253_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 5);
lean_ctor_set(v___x_259_, 1, v_x_253_);
lean_ctor_set(v___x_259_, 0, v_x_254_);
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_x_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_x_253_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_256_);
v___x_264_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5_spec__9(v_x_253_, v___x_264_, v_tail_257_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v___x_270_; 
lean_dec(v_x_269_);
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v_tail_271_; 
v_tail_271_ = lean_ctor_get(v_x_268_, 1);
if (lean_obj_tag(v_tail_271_) == 0)
{
lean_object* v_head_272_; lean_object* v___x_273_; 
lean_dec(v_x_269_);
v_head_272_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_head_272_);
lean_dec_ref_known(v_x_268_, 2);
v___x_273_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_272_);
return v___x_273_;
}
else
{
lean_object* v_head_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc(v_tail_271_);
v_head_274_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_head_274_);
lean_dec_ref_known(v_x_268_, 2);
v___x_275_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_head_274_);
v___x_276_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3_spec__5(v_x_269_, v___x_275_, v_tail_271_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(lean_object* v_xs_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = lean_array_get_size(v_xs_277_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_nat_dec_eq(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_281_ = lean_array_to_list(v_xs_277_);
v___x_282_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__3));
v___x_283_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__3(v___x_281_, v___x_282_);
v___x_284_ = lean_obj_once(&l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6, &l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6_once, _init_l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__6);
v___x_285_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__7));
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_283_);
v___x_287_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__8));
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_284_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l_Std_Format_fill(v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; 
lean_dec_ref(v_xs_277_);
v___x_291_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__10));
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(lean_object* v_b_292_, lean_object* v_acc_293_, lean_object* v_i_294_){
_start:
{
lean_object* v_keyArray_299_; lean_object* v_valueArray_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_keyArray_299_ = lean_ctor_get(v_b_292_, 1);
v_valueArray_300_ = lean_ctor_get(v_b_292_, 2);
v___x_301_ = lean_array_get_size(v_keyArray_299_);
v___x_302_ = lean_nat_dec_lt(v_i_294_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v_i_294_);
lean_inc(v_acc_293_);
return v_acc_293_;
}
else
{
lean_object* v___x_303_; uint8_t v_isSome_304_; 
v___x_303_ = lean_array_fget_borrowed(v_keyArray_299_, v_i_294_);
v_isSome_304_ = lean_noption_is_some(v___x_303_);
if (v_isSome_304_ == 0)
{
goto v___jp_295_;
}
else
{
lean_object* v___x_305_; uint8_t v_isSome_306_; 
v___x_305_ = lean_array_fget_borrowed(v_valueArray_300_, v_i_294_);
v_isSome_306_ = lean_noption_is_some(v___x_305_);
if (v_isSome_306_ == 0)
{
goto v___jp_295_;
}
else
{
lean_object* v_val_307_; lean_object* v_val_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_inc(v___x_303_);
v_val_307_ = lean_noption_get(v___x_303_);
lean_inc(v___x_305_);
v_val_308_ = lean_noption_get(v___x_305_);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_i_294_, v___x_309_);
lean_dec(v_i_294_);
v___x_311_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_b_292_, v_acc_293_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_val_307_);
lean_ctor_set(v___x_312_, 1, v_val_308_);
v___x_313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
}
v___jp_295_:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_i_294_, v___x_296_);
lean_dec(v_i_294_);
v_i_294_ = v___x_297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1___boxed(lean_object* v_b_314_, lean_object* v_acc_315_, lean_object* v_i_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_b_314_, v_acc_315_, v_i_316_);
lean_dec(v_acc_315_);
lean_dec_ref(v_b_314_);
return v_res_317_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(11u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__0));
v___x_347_ = lean_string_length(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__17);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(lean_object* v_x_354_){
_start:
{
lean_object* v_entries_355_; lean_object* v_indexes_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_401_; 
v_entries_355_ = lean_ctor_get(v_x_354_, 0);
v_indexes_356_ = lean_ctor_get(v_x_354_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_354_);
if (v_isSharedCheck_401_ == 0)
{
v___x_358_ = v_x_354_;
v_isShared_359_ = v_isSharedCheck_401_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_indexes_356_);
lean_inc(v_entries_355_);
lean_dec(v_x_354_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_401_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_360_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__5));
v___x_361_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__6));
v___x_362_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__7);
v___x_363_ = l_Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0(v_entries_355_);
if (v_isShared_359_ == 0)
{
lean_ctor_set_tag(v___x_358_, 4);
lean_ctor_set(v___x_358_, 1, v___x_363_);
lean_ctor_set(v___x_358_, 0, v___x_362_);
v___x_365_ = v___x_358_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_400_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_366_ = 0;
v___x_367_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_366_);
v___x_368_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_361_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = ((lean_object*)(l_Array_repr___at___00Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6_spec__9___closed__2));
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_box(1);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__9));
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_360_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__11));
v___x_378_ = lean_box(0);
v___x_379_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__1(v_indexes_356_, v___x_378_, v___x_376_);
lean_dec_ref(v_indexes_356_);
v___x_380_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg(v___x_379_);
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_377_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = l_Repr_addAppParen(v___x_381_, v___x_376_);
v___x_383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_362_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*1, v___x_366_);
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_375_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_369_);
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_371_);
v___x_388_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__13));
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_360_);
v___x_391_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__15));
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_394_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___x_392_);
v___x_396_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_397_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_393_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*1, v___x_366_);
return v___x_399_;
}
}
}
}
static lean_object* _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(7u);
v___x_412_ = lean_nat_to_int(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___redArg(lean_object* v_x_413_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_414_ = ((lean_object*)(l_Std_Http_instReprHeaders_repr___redArg___closed__3));
v___x_415_ = lean_obj_once(&l_Std_Http_instReprHeaders_repr___redArg___closed__4, &l_Std_Http_instReprHeaders_repr___redArg___closed__4_once, _init_l_Std_Http_instReprHeaders_repr___redArg___closed__4);
v___x_416_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_413_);
v___x_417_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = 0;
v___x_419_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*1, v___x_418_);
v___x_420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_414_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18, &l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__18);
v___x_422_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__19));
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_420_);
v___x_424_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg___closed__20));
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_421_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_427_, sizeof(void*)*1, v___x_418_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr(lean_object* v_x_428_, lean_object* v_prec_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_Http_instReprHeaders_repr___redArg(v_x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instReprHeaders_repr___boxed(lean_object* v_x_431_, lean_object* v_prec_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Http_instReprHeaders_repr(v_x_431_, v_prec_432_);
lean_dec(v_prec_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(lean_object* v_x_434_, lean_object* v_prec_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___redArg(v_x_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0___boxed(lean_object* v_x_437_, lean_object* v_prec_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0(v_x_437_, v_prec_438_);
lean_dec(v_prec_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(lean_object* v_a_440_, lean_object* v_n_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___redArg(v_a_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2___boxed(lean_object* v_a_443_, lean_object* v_n_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2(v_a_443_, v_n_444_);
lean_dec(v_n_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___redArg(v_x_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2___boxed(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Prod_repr___at___00Array_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__0_spec__2(v_x_449_, v_x_450_);
lean_dec(v_x_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___redArg(v_x_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Prod_repr___at___00List_repr___at___00Std_Internal_instReprIndexMultiMap_repr___at___00Std_Http_instReprHeaders_repr_spec__0_spec__2_spec__6(v_x_455_, v_x_456_);
lean_dec(v_x_456_);
return v_res_457_;
}
}
static lean_object* _init_l_Std_Http_instMembershipNameHeaders(void){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_instDecidableMemNameHeaders(lean_object* v_name_463_, lean_object* v_h_464_){
_start:
{
lean_object* v___f_465_; lean_object* v___f_466_; uint8_t v___x_467_; 
v___f_465_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_466_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_467_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_465_, v___f_466_, v_name_463_, v_h_464_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instDecidableMemNameHeaders___boxed(lean_object* v_name_468_, lean_object* v_h_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Std_Http_instDecidableMemNameHeaders(v_name_468_, v_h_469_);
lean_dec_ref(v_h_469_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg(lean_object* v_headers_472_, lean_object* v_name_473_){
_start:
{
lean_object* v_entries_474_; lean_object* v_indexes_475_; lean_object* v___f_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v_val_479_; lean_object* v___x_480_; lean_object* v_entry_481_; lean_object* v___x_482_; lean_object* v_snd_483_; 
v_entries_474_ = lean_ctor_get(v_headers_472_, 0);
v_indexes_475_ = lean_ctor_get(v_headers_472_, 1);
v___f_476_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_477_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_476_, v___f_477_, v_indexes_475_, v_name_473_);
v_val_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_val_479_);
lean_dec(v___x_478_);
v___x_480_ = lean_unsigned_to_nat(0u);
v_entry_481_ = lean_array_fget(v_val_479_, v___x_480_);
lean_dec(v_val_479_);
v___x_482_ = lean_array_fget_borrowed(v_entries_474_, v_entry_481_);
lean_dec(v_entry_481_);
v_snd_483_ = lean_ctor_get(v___x_482_, 1);
lean_inc(v_snd_483_);
return v_snd_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___redArg___boxed(lean_object* v_headers_484_, lean_object* v_name_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Http_Headers_get___redArg(v_headers_484_, v_name_485_);
lean_dec_ref(v_headers_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get(lean_object* v_headers_487_, lean_object* v_name_488_, lean_object* v_h_489_){
_start:
{
lean_object* v_entries_490_; lean_object* v_indexes_491_; lean_object* v___f_492_; lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v_val_495_; lean_object* v___x_496_; lean_object* v_entry_497_; lean_object* v___x_498_; lean_object* v_snd_499_; 
v_entries_490_ = lean_ctor_get(v_headers_487_, 0);
v_indexes_491_ = lean_ctor_get(v_headers_487_, 1);
v___f_492_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_493_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_492_, v___f_493_, v_indexes_491_, v_name_488_);
v_val_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_val_495_);
lean_dec(v___x_494_);
v___x_496_ = lean_unsigned_to_nat(0u);
v_entry_497_ = lean_array_fget(v_val_495_, v___x_496_);
lean_dec(v_val_495_);
v___x_498_ = lean_array_fget_borrowed(v_entries_490_, v_entry_497_);
lean_dec(v_entry_497_);
v_snd_499_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_snd_499_);
return v_snd_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get___boxed(lean_object* v_headers_500_, lean_object* v_name_501_, lean_object* v_h_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Http_Headers_get(v_headers_500_, v_name_501_, v_h_502_);
lean_dec_ref(v_headers_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0(lean_object* v_val_504_, lean_object* v_entries_505_, lean_object* v_x1_506_, lean_object* v_x2_507_, lean_object* v_x3_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_snd_511_; 
v___x_509_ = lean_array_fget_borrowed(v_val_504_, v_x1_506_);
v___x_510_ = lean_array_fget_borrowed(v_entries_505_, v___x_509_);
v_snd_511_ = lean_ctor_get(v___x_510_, 1);
lean_inc(v_snd_511_);
return v_snd_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg___lam__0___boxed(lean_object* v_val_512_, lean_object* v_entries_513_, lean_object* v_x1_514_, lean_object* v_x2_515_, lean_object* v_x3_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Http_Headers_getAll___redArg___lam__0(v_val_512_, v_entries_513_, v_x1_514_, v_x2_515_, v_x3_516_);
lean_dec(v_x2_515_);
lean_dec(v_x1_514_);
lean_dec_ref(v_entries_513_);
lean_dec_ref(v_val_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll___redArg(lean_object* v_headers_537_, lean_object* v_name_538_){
_start:
{
lean_object* v_entries_539_; lean_object* v_indexes_540_; lean_object* v___f_541_; lean_object* v___f_542_; lean_object* v___x_543_; lean_object* v_val_544_; lean_object* v___f_545_; lean_object* v___x_546_; size_t v_sz_547_; size_t v___x_548_; lean_object* v_entries_549_; 
v_entries_539_ = lean_ctor_get(v_headers_537_, 0);
lean_inc_ref(v_entries_539_);
v_indexes_540_ = lean_ctor_get(v_headers_537_, 1);
lean_inc_ref(v_indexes_540_);
lean_dec_ref(v_headers_537_);
v___f_541_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_542_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_541_, v___f_542_, v_indexes_540_, v_name_538_);
lean_dec_ref(v_indexes_540_);
v_val_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc_n(v_val_544_, 3);
lean_dec(v___x_543_);
v___f_545_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_545_, 0, v_val_544_);
lean_closure_set(v___f_545_, 1, v_entries_539_);
v___x_546_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_547_ = lean_array_size(v_val_544_);
v___x_548_ = ((size_t)0ULL);
v_entries_549_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_546_, v_val_544_, v___f_545_, v_sz_547_, v___x_548_, v_val_544_);
lean_dec(v_val_544_);
return v_entries_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll(lean_object* v_headers_550_, lean_object* v_name_551_, lean_object* v_h_552_){
_start:
{
lean_object* v_entries_553_; lean_object* v_indexes_554_; lean_object* v___f_555_; lean_object* v___f_556_; lean_object* v___x_557_; lean_object* v_val_558_; lean_object* v___f_559_; lean_object* v___x_560_; size_t v_sz_561_; size_t v___x_562_; lean_object* v_entries_563_; 
v_entries_553_ = lean_ctor_get(v_headers_550_, 0);
lean_inc_ref(v_entries_553_);
v_indexes_554_ = lean_ctor_get(v_headers_550_, 1);
lean_inc_ref(v_indexes_554_);
lean_dec_ref(v_headers_550_);
v___f_555_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_556_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_555_, v___f_556_, v_indexes_554_, v_name_551_);
lean_dec_ref(v_indexes_554_);
v_val_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc_n(v_val_558_, 3);
lean_dec(v___x_557_);
v___f_559_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_559_, 0, v_val_558_);
lean_closure_set(v___f_559_, 1, v_entries_553_);
v___x_560_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_561_ = lean_array_size(v_val_558_);
v___x_562_ = ((size_t)0ULL);
v_entries_563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_560_, v_val_558_, v___f_559_, v_sz_561_, v___x_562_, v_val_558_);
lean_dec(v_val_558_);
return v_entries_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getAll_x3f(lean_object* v_headers_564_, lean_object* v_name_565_){
_start:
{
lean_object* v___f_566_; lean_object* v___f_567_; uint8_t v___x_568_; 
v___f_566_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_567_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_565_);
v___x_568_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_566_, v___f_567_, v_name_565_, v_headers_564_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec_ref(v_name_565_);
lean_dec_ref(v_headers_564_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
else
{
lean_object* v_entries_570_; lean_object* v_indexes_571_; lean_object* v___x_572_; lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_585_; 
v_entries_570_ = lean_ctor_get(v_headers_564_, 0);
lean_inc_ref(v_entries_570_);
v_indexes_571_ = lean_ctor_get(v_headers_564_, 1);
lean_inc_ref(v_indexes_571_);
lean_dec_ref(v_headers_564_);
v___x_572_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_566_, v___f_567_, v_indexes_571_, v_name_565_);
lean_dec_ref(v_indexes_571_);
v_val_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_585_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___f_577_; lean_object* v___x_578_; size_t v_sz_579_; size_t v___x_580_; lean_object* v_entries_581_; lean_object* v___x_583_; 
lean_inc_n(v_val_573_, 2);
v___f_577_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_577_, 0, v_val_573_);
lean_closure_set(v___f_577_, 1, v_entries_570_);
v___x_578_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_579_ = lean_array_size(v_val_573_);
v___x_580_ = ((size_t)0ULL);
v_entries_581_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_578_, v_val_573_, v___f_577_, v_sz_579_, v___x_580_, v_val_573_);
lean_dec(v_val_573_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v_entries_581_);
v___x_583_ = v___x_575_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_entries_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f(lean_object* v_headers_586_, lean_object* v_name_587_){
_start:
{
lean_object* v___f_588_; lean_object* v___f_589_; uint8_t v___x_590_; 
v___f_588_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_589_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_587_);
v___x_590_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_588_, v___f_589_, v_name_587_, v_headers_586_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_name_587_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
lean_object* v_entries_592_; lean_object* v_indexes_593_; lean_object* v___x_594_; lean_object* v_val_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_606_; 
v_entries_592_ = lean_ctor_get(v_headers_586_, 0);
v_indexes_593_ = lean_ctor_get(v_headers_586_, 1);
v___x_594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_588_, v___f_589_, v_indexes_593_, v_name_587_);
v_val_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_606_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_val_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v_entry_600_; lean_object* v___x_601_; lean_object* v_snd_602_; lean_object* v___x_604_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v_entry_600_ = lean_array_fget(v_val_595_, v___x_599_);
lean_dec(v_val_595_);
v___x_601_ = lean_array_fget_borrowed(v_entries_592_, v_entry_600_);
lean_dec(v_entry_600_);
v_snd_602_ = lean_ctor_get(v___x_601_, 1);
lean_inc(v_snd_602_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_snd_602_);
v___x_604_ = v___x_597_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_snd_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x3f___boxed(lean_object* v_headers_607_, lean_object* v_name_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Http_Headers_get_x3f(v_headers_607_, v_name_608_);
lean_dec_ref(v_headers_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1(lean_object* v_value_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_a_613_, lean_object* v_x_614_, lean_object* v___y_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = l_Std_Http_Header_instBEqValue_beq(v_a_613_, v_value_610_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_dec_ref(v_a_613_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_611_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v___x_611_);
v___x_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_618_, 0, v_a_613_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_612_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___lam__1___boxed(lean_object* v_value_622_, lean_object* v___x_623_, lean_object* v___x_624_, lean_object* v_a_625_, lean_object* v_x_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Http_Headers_hasEntry___lam__1(v_value_622_, v___x_623_, v___x_624_, v_a_625_, v_x_626_, v___y_627_);
lean_dec_ref(v___y_627_);
lean_dec_ref(v_value_622_);
return v_res_628_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_hasEntry(lean_object* v_headers_632_, lean_object* v_name_633_, lean_object* v_value_634_){
_start:
{
lean_object* v___f_635_; lean_object* v___f_636_; uint8_t v___x_637_; 
v___f_635_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_636_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_633_);
v___x_637_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_635_, v___f_636_, v_name_633_, v_headers_632_);
if (v___x_637_ == 0)
{
lean_dec_ref(v_value_634_);
lean_dec_ref(v_name_633_);
lean_dec_ref(v_headers_632_);
return v___x_637_;
}
else
{
lean_object* v_entries_638_; lean_object* v_indexes_639_; lean_object* v___x_640_; lean_object* v_val_641_; lean_object* v___f_642_; lean_object* v___x_643_; size_t v_sz_644_; size_t v___x_645_; lean_object* v_entries_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___f_649_; size_t v_sz_650_; lean_object* v___x_651_; lean_object* v_fst_652_; 
v_entries_638_ = lean_ctor_get(v_headers_632_, 0);
lean_inc_ref(v_entries_638_);
v_indexes_639_ = lean_ctor_get(v_headers_632_, 1);
lean_inc_ref(v_indexes_639_);
lean_dec_ref(v_headers_632_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_635_, v___f_636_, v_indexes_639_, v_name_633_);
lean_dec_ref(v_indexes_639_);
v_val_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc_n(v_val_641_, 3);
lean_dec(v___x_640_);
v___f_642_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_642_, 0, v_val_641_);
lean_closure_set(v___f_642_, 1, v_entries_638_);
v___x_643_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_644_ = lean_array_size(v_val_641_);
v___x_645_ = ((size_t)0ULL);
v_entries_646_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_643_, v_val_641_, v___f_642_, v_sz_644_, v___x_645_, v_val_641_);
lean_dec(v_val_641_);
v___x_647_ = lean_box(0);
v___x_648_ = ((lean_object*)(l_Std_Http_Headers_hasEntry___closed__0));
v___f_649_ = lean_alloc_closure((void*)(l_Std_Http_Headers_hasEntry___lam__1___boxed), 6, 3);
lean_closure_set(v___f_649_, 0, v_value_634_);
lean_closure_set(v___f_649_, 1, v___x_648_);
lean_closure_set(v___f_649_, 2, v___x_647_);
v_sz_650_ = lean_array_size(v_entries_646_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_643_, v_entries_646_, v___f_649_, v_sz_650_, v___x_645_, v___x_648_);
v_fst_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_fst_652_);
lean_dec(v___x_651_);
if (lean_obj_tag(v_fst_652_) == 0)
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
else
{
lean_object* v_val_654_; 
v_val_654_ = lean_ctor_get(v_fst_652_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v_fst_652_, 1);
if (lean_obj_tag(v_val_654_) == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
else
{
lean_dec_ref_known(v_val_654_, 1);
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_hasEntry___boxed(lean_object* v_headers_656_, lean_object* v_name_657_, lean_object* v_value_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Std_Http_Headers_hasEntry(v_headers_656_, v_name_657_, v_value_658_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getLast_x3f(lean_object* v_headers_661_, lean_object* v_name_662_){
_start:
{
lean_object* v___f_663_; lean_object* v___f_664_; uint8_t v___x_665_; 
v___f_663_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_664_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_662_);
v___x_665_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_663_, v___f_664_, v_name_662_, v_headers_661_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec_ref(v_name_662_);
lean_dec_ref(v_headers_661_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v_entries_667_; lean_object* v_indexes_668_; lean_object* v___x_669_; lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_688_; 
v_entries_667_ = lean_ctor_get(v_headers_661_, 0);
lean_inc_ref(v_entries_667_);
v_indexes_668_ = lean_ctor_get(v_headers_661_, 1);
lean_inc_ref(v_indexes_668_);
lean_dec_ref(v_headers_661_);
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_663_, v___f_664_, v_indexes_668_, v_name_662_);
lean_dec_ref(v_indexes_668_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_688_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_688_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_688_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___f_674_; lean_object* v___x_675_; size_t v_sz_676_; size_t v___x_677_; lean_object* v_entries_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
lean_inc_n(v_val_670_, 2);
v___f_674_ = lean_alloc_closure((void*)(l_Std_Http_Headers_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_674_, 0, v_val_670_);
lean_closure_set(v___f_674_, 1, v_entries_667_);
v___x_675_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_676_ = lean_array_size(v_val_670_);
v___x_677_ = ((size_t)0ULL);
v_entries_678_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_675_, v_val_670_, v___f_674_, v_sz_676_, v___x_677_, v_val_670_);
lean_dec(v_val_670_);
v___x_679_ = lean_array_get_size(v_entries_678_);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_sub(v___x_679_, v___x_680_);
v___x_682_ = lean_nat_dec_lt(v___x_681_, v___x_679_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec(v___x_681_);
lean_dec(v_entries_678_);
lean_del_object(v___x_672_);
v___x_683_ = lean_box(0);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_array_fget(v_entries_678_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v_entries_678_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_684_);
v___x_686_ = v___x_672_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD(lean_object* v_headers_689_, lean_object* v_name_690_, lean_object* v_d_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___f_693_; uint8_t v___x_694_; 
v___f_692_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_693_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_690_);
v___x_694_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_692_, v___f_693_, v_name_690_, v_headers_689_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_name_690_);
lean_inc_ref(v_d_691_);
return v_d_691_;
}
else
{
lean_object* v_entries_695_; lean_object* v_indexes_696_; lean_object* v___x_697_; lean_object* v_val_698_; lean_object* v___x_699_; lean_object* v_entry_700_; lean_object* v___x_701_; lean_object* v_snd_702_; 
v_entries_695_ = lean_ctor_get(v_headers_689_, 0);
v_indexes_696_ = lean_ctor_get(v_headers_689_, 1);
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_692_, v___f_693_, v_indexes_696_, v_name_690_);
v_val_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_698_);
lean_dec(v___x_697_);
v___x_699_ = lean_unsigned_to_nat(0u);
v_entry_700_ = lean_array_fget(v_val_698_, v___x_699_);
lean_dec(v_val_698_);
v___x_701_ = lean_array_fget_borrowed(v_entries_695_, v_entry_700_);
lean_dec(v_entry_700_);
v_snd_702_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_snd_702_);
return v_snd_702_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_getD___boxed(lean_object* v_headers_703_, lean_object* v_name_704_, lean_object* v_d_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_Http_Headers_getD(v_headers_703_, v_name_704_, v_d_705_);
lean_dec_ref(v_d_705_);
lean_dec_ref(v_headers_703_);
return v_res_706_;
}
}
static lean_object* _init_l_Std_Http_Headers_get_x21___closed__4(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_711_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__3));
v___x_712_ = lean_unsigned_to_nat(14u);
v___x_713_ = lean_unsigned_to_nat(22u);
v___x_714_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__2));
v___x_715_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__1));
v___x_716_ = l_mkPanicMessageWithDecl(v___x_715_, v___x_714_, v___x_713_, v___x_712_, v___x_711_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21(lean_object* v_headers_717_, lean_object* v_name_718_){
_start:
{
lean_object* v___f_719_; lean_object* v___f_720_; uint8_t v___x_721_; 
v___f_719_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_720_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_718_);
v___x_721_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_719_, v___f_720_, v_name_718_, v_headers_717_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref(v_name_718_);
v___x_722_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___x_723_ = lean_obj_once(&l_Std_Http_Headers_get_x21___closed__4, &l_Std_Http_Headers_get_x21___closed__4_once, _init_l_Std_Http_Headers_get_x21___closed__4);
v___x_724_ = l_panic___redArg(v___x_722_, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_entries_725_; lean_object* v_indexes_726_; lean_object* v___x_727_; lean_object* v_val_728_; lean_object* v___x_729_; lean_object* v_entry_730_; lean_object* v___x_731_; lean_object* v_snd_732_; 
v_entries_725_ = lean_ctor_get(v_headers_717_, 0);
v_indexes_726_ = lean_ctor_get(v_headers_717_, 1);
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_719_, v___f_720_, v_indexes_726_, v_name_718_);
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec(v___x_727_);
v___x_729_ = lean_unsigned_to_nat(0u);
v_entry_730_ = lean_array_fget(v_val_728_, v___x_729_);
lean_dec(v_val_728_);
v___x_731_ = lean_array_fget_borrowed(v_entries_725_, v_entry_730_);
lean_dec(v_entry_730_);
v_snd_732_ = lean_ctor_get(v___x_731_, 1);
lean_inc(v_snd_732_);
return v_snd_732_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_get_x21___boxed(lean_object* v_headers_733_, lean_object* v_name_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Http_Headers_get_x21(v_headers_733_, v_name_734_);
lean_dec_ref(v_headers_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert___lam__0(lean_object* v_i_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_mk_empty_array_with_capacity(v___x_738_);
v___x_740_ = lean_array_push(v___x_739_, v_i_736_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_val_742_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v_x_737_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v_x_737_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_array_push(v_val_742_, v_i_736_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert(lean_object* v_headers_751_, lean_object* v_key_752_, lean_object* v_value_753_){
_start:
{
lean_object* v_entries_754_; lean_object* v_indexes_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_852_; 
v_entries_754_ = lean_ctor_get(v_headers_751_, 0);
v_indexes_755_ = lean_ctor_get(v_headers_751_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_headers_751_);
if (v_isSharedCheck_852_ == 0)
{
v___x_757_ = v_headers_751_;
v_isShared_758_ = v_isSharedCheck_852_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_indexes_755_);
lean_inc(v_entries_754_);
lean_dec(v_headers_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_852_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v_i_761_; lean_object* v___x_762_; lean_object* v_entries_763_; lean_object* v___x_764_; 
v___f_759_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_760_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_761_ = lean_array_get_size(v_entries_754_);
lean_inc_ref_n(v_key_752_, 2);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_key_752_);
lean_ctor_set(v___x_762_, 1, v_value_753_);
v_entries_763_ = lean_array_push(v_entries_754_, v___x_762_);
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_759_, v___f_760_, v_indexes_755_, v_key_752_);
switch(lean_obj_tag(v___x_764_))
{
case 0:
{
lean_object* v_index_765_; lean_object* v_value_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_val_769_; lean_object* v_size_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v_index_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_index_765_);
v_value_766_ = lean_ctor_get(v___x_764_, 2);
lean_inc(v_value_766_);
lean_dec_ref_known(v___x_764_, 3);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v_value_766_);
v___x_768_ = l_Std_Http_Headers_insert___lam__0(v_i_761_, v___x_767_);
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec(v___x_768_);
v_size_770_ = lean_ctor_get(v_indexes_755_, 0);
lean_inc(v_size_770_);
v___x_771_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_755_, v_size_770_, v_index_765_, v_key_752_, v_val_769_);
lean_dec(v_index_765_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_771_);
lean_ctor_set(v___x_757_, 0, v_entries_763_);
v___x_773_ = v___x_757_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_entries_763_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
case 1:
{
lean_object* v_index_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_val_778_; lean_object* v___y_780_; lean_object* v_i_781_; lean_object* v_size_801_; lean_object* v_keyArray_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_index_775_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_index_775_);
lean_dec_ref_known(v___x_764_, 1);
v___x_776_ = lean_box(0);
v___x_777_ = l_Std_Http_Headers_insert___lam__0(v_i_761_, v___x_776_);
v_val_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_778_);
lean_dec(v___x_777_);
v_size_801_ = lean_ctor_get(v_indexes_755_, 0);
v_keyArray_802_ = lean_ctor_get(v_indexes_755_, 1);
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_add(v_size_801_, v___x_803_);
v___x_805_ = lean_array_get_size(v_keyArray_802_);
v___x_806_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_dec(v___x_804_);
lean_dec(v_index_775_);
goto v___jp_789_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_807_ = lean_unsigned_to_nat(4u);
v___x_808_ = lean_nat_mul(v___x_804_, v___x_807_);
v___x_809_ = lean_unsigned_to_nat(3u);
v___x_810_ = lean_nat_mul(v___x_805_, v___x_809_);
v___x_811_ = lean_nat_dec_le(v___x_808_, v___x_810_);
lean_dec(v___x_810_);
lean_dec(v___x_808_);
if (v___x_811_ == 0)
{
lean_dec(v___x_804_);
lean_dec(v_index_775_);
goto v___jp_789_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_del_object(v___x_757_);
v___x_812_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_755_, v___x_804_, v_index_775_, v_key_752_, v_val_778_);
lean_dec(v_index_775_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_entries_763_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
}
v___jp_779_:
{
lean_object* v_size_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_size_782_ = lean_ctor_get(v___y_780_, 0);
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_size_782_, v___x_783_);
v___x_785_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_780_, v___x_784_, v_i_781_, v_key_752_, v_val_778_);
lean_dec(v_i_781_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_785_);
lean_ctor_set(v___x_757_, 0, v_entries_763_);
v___x_787_ = v___x_757_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_entries_763_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
v___jp_789_:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_759_, v___f_760_, v_indexes_755_);
lean_inc_ref(v_key_752_);
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_759_, v___f_760_, v___x_790_, v_key_752_);
switch(lean_obj_tag(v___x_791_))
{
case 0:
{
lean_object* v_index_792_; lean_object* v_size_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
lean_del_object(v___x_757_);
v_index_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_index_792_);
lean_dec_ref_known(v___x_791_, 3);
v_size_793_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_size_793_);
v___x_794_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_790_, v_size_793_, v_index_792_, v_key_752_, v_val_778_);
lean_dec(v_index_792_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v_entries_763_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
return v___x_795_;
}
case 1:
{
lean_object* v_index_796_; 
v_index_796_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_index_796_);
lean_dec_ref_known(v___x_791_, 1);
v___y_780_ = v___x_790_;
v_i_781_ = v_index_796_;
goto v___jp_779_;
}
default: 
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_790_, v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_index_799_; 
v_index_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_index_799_);
lean_dec_ref_known(v___x_798_, 1);
v___y_780_ = v___x_790_;
v_i_781_ = v_index_799_;
goto v___jp_779_;
}
else
{
lean_object* v___x_800_; 
lean_dec(v_val_778_);
lean_del_object(v___x_757_);
lean_dec_ref(v_key_752_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_entries_763_);
lean_ctor_set(v___x_800_, 1, v___x_790_);
return v___x_800_;
}
}
}
}
}
default: 
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_val_816_; lean_object* v___y_818_; lean_object* v_i_819_; lean_object* v___y_828_; lean_object* v_size_839_; lean_object* v_keyArray_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_814_ = lean_box(0);
v___x_815_ = l_Std_Http_Headers_insert___lam__0(v_i_761_, v___x_814_);
v_val_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_val_816_);
lean_dec(v___x_815_);
v_size_839_ = lean_ctor_get(v_indexes_755_, 0);
v_keyArray_840_ = lean_ctor_get(v_indexes_755_, 1);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_size_839_, v___x_841_);
v___x_843_ = lean_array_get_size(v_keyArray_840_);
v___x_844_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v___x_842_);
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_759_, v___f_760_, v_indexes_755_);
v___y_828_ = v___x_845_;
goto v___jp_827_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_846_ = lean_unsigned_to_nat(4u);
v___x_847_ = lean_nat_mul(v___x_842_, v___x_846_);
lean_dec(v___x_842_);
v___x_848_ = lean_unsigned_to_nat(3u);
v___x_849_ = lean_nat_mul(v___x_843_, v___x_848_);
v___x_850_ = lean_nat_dec_le(v___x_847_, v___x_849_);
lean_dec(v___x_849_);
lean_dec(v___x_847_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
v___x_851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_759_, v___f_760_, v_indexes_755_);
v___y_828_ = v___x_851_;
goto v___jp_827_;
}
else
{
v___y_828_ = v_indexes_755_;
goto v___jp_827_;
}
}
v___jp_817_:
{
lean_object* v_size_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v_size_820_ = lean_ctor_get(v___y_818_, 0);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_size_820_, v___x_821_);
v___x_823_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_818_, v___x_822_, v_i_819_, v_key_752_, v_val_816_);
lean_dec(v_i_819_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 1, v___x_823_);
lean_ctor_set(v___x_757_, 0, v_entries_763_);
v___x_825_ = v___x_757_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_entries_763_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
v___jp_827_:
{
lean_object* v___x_829_; 
lean_inc_ref(v_key_752_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_759_, v___f_760_, v___y_828_, v_key_752_);
switch(lean_obj_tag(v___x_829_))
{
case 0:
{
lean_object* v_index_830_; lean_object* v_size_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_757_);
v_index_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_index_830_);
lean_dec_ref_known(v___x_829_, 3);
v_size_831_ = lean_ctor_get(v___y_828_, 0);
lean_inc(v_size_831_);
v___x_832_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_828_, v_size_831_, v_index_830_, v_key_752_, v_val_816_);
lean_dec(v_index_830_);
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v_entries_763_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
return v___x_833_;
}
case 1:
{
lean_object* v_index_834_; 
v_index_834_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_index_834_);
lean_dec_ref_known(v___x_829_, 1);
v___y_818_ = v___y_828_;
v_i_819_ = v_index_834_;
goto v___jp_817_;
}
default: 
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_828_, v___x_835_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_index_837_; 
v_index_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_index_837_);
lean_dec_ref_known(v___x_836_, 1);
v___y_818_ = v___y_828_;
v_i_819_ = v_index_837_;
goto v___jp_817_;
}
else
{
lean_object* v___x_838_; 
lean_dec(v_val_816_);
lean_del_object(v___x_757_);
lean_dec_ref(v_key_752_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_entries_763_);
lean_ctor_set(v___x_838_, 1, v___y_828_);
return v___x_838_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x21(lean_object* v_headers_853_, lean_object* v_name_854_, lean_object* v_value_855_){
_start:
{
lean_object* v_entries_856_; lean_object* v_indexes_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_956_; 
v_entries_856_ = lean_ctor_get(v_headers_853_, 0);
v_indexes_857_ = lean_ctor_get(v_headers_853_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_headers_853_);
if (v_isSharedCheck_956_ == 0)
{
v___x_859_ = v_headers_853_;
v_isShared_860_ = v_isSharedCheck_956_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_indexes_857_);
lean_inc(v_entries_856_);
lean_dec(v_headers_853_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_956_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v_i_865_; lean_object* v___x_866_; lean_object* v_entries_867_; lean_object* v___x_868_; 
v___x_861_ = l_Std_Http_Header_Name_ofString_x21(v_name_854_);
v___x_862_ = l_Std_Http_Header_Value_ofString_x21(v_value_855_);
v___f_863_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_864_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_865_ = lean_array_get_size(v_entries_856_);
lean_inc_ref_n(v___x_861_, 2);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_861_);
lean_ctor_set(v___x_866_, 1, v___x_862_);
v_entries_867_ = lean_array_push(v_entries_856_, v___x_866_);
v___x_868_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_863_, v___f_864_, v_indexes_857_, v___x_861_);
switch(lean_obj_tag(v___x_868_))
{
case 0:
{
lean_object* v_index_869_; lean_object* v_value_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_val_873_; lean_object* v_size_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v_index_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_index_869_);
v_value_870_ = lean_ctor_get(v___x_868_, 2);
lean_inc(v_value_870_);
lean_dec_ref_known(v___x_868_, 3);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v_value_870_);
v___x_872_ = l_Std_Http_Headers_insert___lam__0(v_i_865_, v___x_871_);
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec(v___x_872_);
v_size_874_ = lean_ctor_get(v_indexes_857_, 0);
lean_inc(v_size_874_);
v___x_875_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_857_, v_size_874_, v_index_869_, v___x_861_, v_val_873_);
lean_dec(v_index_869_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_875_);
lean_ctor_set(v___x_859_, 0, v_entries_867_);
v___x_877_ = v___x_859_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_entries_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
case 1:
{
lean_object* v_index_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_val_882_; lean_object* v___y_884_; lean_object* v_i_885_; lean_object* v_size_905_; lean_object* v_keyArray_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_index_879_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_index_879_);
lean_dec_ref_known(v___x_868_, 1);
v___x_880_ = lean_box(0);
v___x_881_ = l_Std_Http_Headers_insert___lam__0(v_i_865_, v___x_880_);
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec(v___x_881_);
v_size_905_ = lean_ctor_get(v_indexes_857_, 0);
v_keyArray_906_ = lean_ctor_get(v_indexes_857_, 1);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_nat_add(v_size_905_, v___x_907_);
v___x_909_ = lean_array_get_size(v_keyArray_906_);
v___x_910_ = lean_nat_dec_lt(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec(v___x_908_);
lean_dec(v_index_879_);
goto v___jp_893_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_911_ = lean_unsigned_to_nat(4u);
v___x_912_ = lean_nat_mul(v___x_908_, v___x_911_);
v___x_913_ = lean_unsigned_to_nat(3u);
v___x_914_ = lean_nat_mul(v___x_909_, v___x_913_);
v___x_915_ = lean_nat_dec_le(v___x_912_, v___x_914_);
lean_dec(v___x_914_);
lean_dec(v___x_912_);
if (v___x_915_ == 0)
{
lean_dec(v___x_908_);
lean_dec(v_index_879_);
goto v___jp_893_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_859_);
v___x_916_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_857_, v___x_908_, v_index_879_, v___x_861_, v_val_882_);
lean_dec(v_index_879_);
v___x_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_917_, 0, v_entries_867_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
return v___x_917_;
}
}
v___jp_883_:
{
lean_object* v_size_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v_size_886_ = lean_ctor_get(v___y_884_, 0);
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_nat_add(v_size_886_, v___x_887_);
v___x_889_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_884_, v___x_888_, v_i_885_, v___x_861_, v_val_882_);
lean_dec(v_i_885_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_889_);
lean_ctor_set(v___x_859_, 0, v_entries_867_);
v___x_891_ = v___x_859_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_entries_867_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
v___jp_893_:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_863_, v___f_864_, v_indexes_857_);
lean_inc_ref(v___x_861_);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_863_, v___f_864_, v___x_894_, v___x_861_);
switch(lean_obj_tag(v___x_895_))
{
case 0:
{
lean_object* v_index_896_; lean_object* v_size_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_del_object(v___x_859_);
v_index_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_index_896_);
lean_dec_ref_known(v___x_895_, 3);
v_size_897_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_size_897_);
v___x_898_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_894_, v_size_897_, v_index_896_, v___x_861_, v_val_882_);
lean_dec(v_index_896_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v_entries_867_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
case 1:
{
lean_object* v_index_900_; 
v_index_900_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_index_900_);
lean_dec_ref_known(v___x_895_, 1);
v___y_884_ = v___x_894_;
v_i_885_ = v_index_900_;
goto v___jp_883_;
}
default: 
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_894_, v___x_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_index_903_; 
v_index_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_index_903_);
lean_dec_ref_known(v___x_902_, 1);
v___y_884_ = v___x_894_;
v_i_885_ = v_index_903_;
goto v___jp_883_;
}
else
{
lean_object* v___x_904_; 
lean_dec(v_val_882_);
lean_dec_ref(v___x_861_);
lean_del_object(v___x_859_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_entries_867_);
lean_ctor_set(v___x_904_, 1, v___x_894_);
return v___x_904_;
}
}
}
}
}
default: 
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_val_920_; lean_object* v___y_922_; lean_object* v_i_923_; lean_object* v___y_932_; lean_object* v_size_943_; lean_object* v_keyArray_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_918_ = lean_box(0);
v___x_919_ = l_Std_Http_Headers_insert___lam__0(v_i_865_, v___x_918_);
v_val_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_val_920_);
lean_dec(v___x_919_);
v_size_943_ = lean_ctor_get(v_indexes_857_, 0);
v_keyArray_944_ = lean_ctor_get(v_indexes_857_, 1);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_add(v_size_943_, v___x_945_);
v___x_947_ = lean_array_get_size(v_keyArray_944_);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v___x_946_);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_863_, v___f_864_, v_indexes_857_);
v___y_932_ = v___x_949_;
goto v___jp_931_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_950_ = lean_unsigned_to_nat(4u);
v___x_951_ = lean_nat_mul(v___x_946_, v___x_950_);
lean_dec(v___x_946_);
v___x_952_ = lean_unsigned_to_nat(3u);
v___x_953_ = lean_nat_mul(v___x_947_, v___x_952_);
v___x_954_ = lean_nat_dec_le(v___x_951_, v___x_953_);
lean_dec(v___x_953_);
lean_dec(v___x_951_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_863_, v___f_864_, v_indexes_857_);
v___y_932_ = v___x_955_;
goto v___jp_931_;
}
else
{
v___y_932_ = v_indexes_857_;
goto v___jp_931_;
}
}
v___jp_921_:
{
lean_object* v_size_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v_size_924_ = lean_ctor_get(v___y_922_, 0);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_size_924_, v___x_925_);
v___x_927_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_922_, v___x_926_, v_i_923_, v___x_861_, v_val_920_);
lean_dec(v_i_923_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_927_);
lean_ctor_set(v___x_859_, 0, v_entries_867_);
v___x_929_ = v___x_859_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_entries_867_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
v___jp_931_:
{
lean_object* v___x_933_; 
lean_inc_ref(v___x_861_);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_863_, v___f_864_, v___y_932_, v___x_861_);
switch(lean_obj_tag(v___x_933_))
{
case 0:
{
lean_object* v_index_934_; lean_object* v_size_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_del_object(v___x_859_);
v_index_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_index_934_);
lean_dec_ref_known(v___x_933_, 3);
v_size_935_ = lean_ctor_get(v___y_932_, 0);
lean_inc(v_size_935_);
v___x_936_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_932_, v_size_935_, v_index_934_, v___x_861_, v_val_920_);
lean_dec(v_index_934_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_entries_867_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
return v___x_937_;
}
case 1:
{
lean_object* v_index_938_; 
v_index_938_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_index_938_);
lean_dec_ref_known(v___x_933_, 1);
v___y_922_ = v___y_932_;
v_i_923_ = v_index_938_;
goto v___jp_921_;
}
default: 
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_932_, v___x_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_index_941_; 
v_index_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_index_941_);
lean_dec_ref_known(v___x_940_, 1);
v___y_922_ = v___y_932_;
v_i_923_ = v_index_941_;
goto v___jp_921_;
}
else
{
lean_object* v___x_942_; 
lean_dec(v_val_920_);
lean_dec_ref(v___x_861_);
lean_del_object(v___x_859_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v_entries_867_);
lean_ctor_set(v___x_942_, 1, v___y_932_);
return v___x_942_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insert_x3f(lean_object* v_headers_957_, lean_object* v_name_958_, lean_object* v_value_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Std_Http_Header_Name_ofString_x3f(v_name_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_961_; 
lean_dec_ref(v_value_959_);
lean_dec_ref(v_headers_957_);
v___x_961_ = lean_box(0);
return v___x_961_;
}
else
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1068_; 
v_val_962_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_964_ = v___x_960_;
v_isShared_965_ = v_isSharedCheck_1068_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v___x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1068_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; 
v___x_966_ = l_Std_Http_Header_Value_ofString_x3f(v_value_959_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; 
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
lean_dec_ref(v_headers_957_);
v___x_967_ = lean_box(0);
return v___x_967_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1067_; 
v_val_968_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_1067_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1067_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_entries_972_; lean_object* v_indexes_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1066_; 
v_entries_972_ = lean_ctor_get(v_headers_957_, 0);
v_indexes_973_ = lean_ctor_get(v_headers_957_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_headers_957_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_975_ = v_headers_957_;
v_isShared_976_ = v_isSharedCheck_1066_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_indexes_973_);
lean_inc(v_entries_972_);
lean_dec(v_headers_957_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1066_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___f_977_; lean_object* v___f_978_; lean_object* v_i_979_; lean_object* v___x_980_; lean_object* v_entries_981_; lean_object* v___y_983_; lean_object* v___x_990_; 
v___f_977_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_978_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_979_ = lean_array_get_size(v_entries_972_);
lean_inc_n(v_val_962_, 2);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v_val_962_);
lean_ctor_set(v___x_980_, 1, v_val_968_);
v_entries_981_ = lean_array_push(v_entries_972_, v___x_980_);
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_977_, v___f_978_, v_indexes_973_, v_val_962_);
switch(lean_obj_tag(v___x_990_))
{
case 0:
{
lean_object* v_index_991_; lean_object* v_value_992_; lean_object* v___x_994_; 
v_index_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_index_991_);
v_value_992_ = lean_ctor_get(v___x_990_, 2);
lean_inc(v_value_992_);
lean_dec_ref_known(v___x_990_, 3);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v_value_992_);
v___x_994_ = v___x_964_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_value_992_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v_val_996_; lean_object* v_size_997_; lean_object* v___x_998_; 
v___x_995_ = l_Std_Http_Headers_insert___lam__0(v_i_979_, v___x_994_);
v_val_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_val_996_);
lean_dec(v___x_995_);
v_size_997_ = lean_ctor_get(v_indexes_973_, 0);
lean_inc(v_size_997_);
v___x_998_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_973_, v_size_997_, v_index_991_, v_val_962_, v_val_996_);
lean_dec(v_index_991_);
v___y_983_ = v___x_998_;
goto v___jp_982_;
}
}
case 1:
{
lean_object* v_index_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_val_1003_; lean_object* v___y_1005_; lean_object* v_i_1006_; lean_object* v_size_1021_; lean_object* v_keyArray_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
lean_del_object(v___x_964_);
v_index_1000_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_index_1000_);
lean_dec_ref_known(v___x_990_, 1);
v___x_1001_ = lean_box(0);
v___x_1002_ = l_Std_Http_Headers_insert___lam__0(v_i_979_, v___x_1001_);
v_val_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_val_1003_);
lean_dec(v___x_1002_);
v_size_1021_ = lean_ctor_get(v_indexes_973_, 0);
v_keyArray_1022_ = lean_ctor_get(v_indexes_973_, 1);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_size_1021_, v___x_1023_);
v___x_1025_ = lean_array_get_size(v_keyArray_1022_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v_index_1000_);
goto v___jp_1011_;
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1027_ = lean_unsigned_to_nat(4u);
v___x_1028_ = lean_nat_mul(v___x_1024_, v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(3u);
v___x_1030_ = lean_nat_mul(v___x_1025_, v___x_1029_);
v___x_1031_ = lean_nat_dec_le(v___x_1028_, v___x_1030_);
lean_dec(v___x_1030_);
lean_dec(v___x_1028_);
if (v___x_1031_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v_index_1000_);
goto v___jp_1011_;
}
else
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_973_, v___x_1024_, v_index_1000_, v_val_962_, v_val_1003_);
lean_dec(v_index_1000_);
v___y_983_ = v___x_1032_;
goto v___jp_982_;
}
}
v___jp_1004_:
{
lean_object* v_size_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_size_1007_ = lean_ctor_get(v___y_1005_, 0);
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_size_1007_, v___x_1008_);
v___x_1010_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1005_, v___x_1009_, v_i_1006_, v_val_962_, v_val_1003_);
lean_dec(v_i_1006_);
v___y_983_ = v___x_1010_;
goto v___jp_982_;
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_977_, v___f_978_, v_indexes_973_);
lean_inc(v_val_962_);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_977_, v___f_978_, v___x_1012_, v_val_962_);
switch(lean_obj_tag(v___x_1013_))
{
case 0:
{
lean_object* v_index_1014_; lean_object* v_size_1015_; lean_object* v___x_1016_; 
v_index_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_index_1014_);
lean_dec_ref_known(v___x_1013_, 3);
v_size_1015_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_size_1015_);
v___x_1016_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1012_, v_size_1015_, v_index_1014_, v_val_962_, v_val_1003_);
lean_dec(v_index_1014_);
v___y_983_ = v___x_1016_;
goto v___jp_982_;
}
case 1:
{
lean_object* v_index_1017_; 
v_index_1017_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_index_1017_);
lean_dec_ref_known(v___x_1013_, 1);
v___y_1005_ = v___x_1012_;
v_i_1006_ = v_index_1017_;
goto v___jp_1004_;
}
default: 
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1012_, v___x_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_index_1020_; 
v_index_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_index_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v___y_1005_ = v___x_1012_;
v_i_1006_ = v_index_1020_;
goto v___jp_1004_;
}
else
{
lean_dec(v_val_1003_);
lean_dec(v_val_962_);
v___y_983_ = v___x_1012_;
goto v___jp_982_;
}
}
}
}
}
default: 
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_val_1035_; lean_object* v___y_1037_; lean_object* v_i_1038_; lean_object* v___y_1044_; lean_object* v_size_1053_; lean_object* v_keyArray_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
lean_del_object(v___x_964_);
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Std_Http_Headers_insert___lam__0(v_i_979_, v___x_1033_);
v_val_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_val_1035_);
lean_dec(v___x_1034_);
v_size_1053_ = lean_ctor_get(v_indexes_973_, 0);
v_keyArray_1054_ = lean_ctor_get(v_indexes_973_, 1);
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_size_1053_, v___x_1055_);
v___x_1057_ = lean_array_get_size(v_keyArray_1054_);
v___x_1058_ = lean_nat_dec_lt(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v___x_1056_);
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_977_, v___f_978_, v_indexes_973_);
v___y_1044_ = v___x_1059_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1060_ = lean_unsigned_to_nat(4u);
v___x_1061_ = lean_nat_mul(v___x_1056_, v___x_1060_);
lean_dec(v___x_1056_);
v___x_1062_ = lean_unsigned_to_nat(3u);
v___x_1063_ = lean_nat_mul(v___x_1057_, v___x_1062_);
v___x_1064_ = lean_nat_dec_le(v___x_1061_, v___x_1063_);
lean_dec(v___x_1063_);
lean_dec(v___x_1061_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_977_, v___f_978_, v_indexes_973_);
v___y_1044_ = v___x_1065_;
goto v___jp_1043_;
}
else
{
v___y_1044_ = v_indexes_973_;
goto v___jp_1043_;
}
}
v___jp_1036_:
{
lean_object* v_size_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_size_1039_ = lean_ctor_get(v___y_1037_, 0);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_add(v_size_1039_, v___x_1040_);
v___x_1042_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1037_, v___x_1041_, v_i_1038_, v_val_962_, v_val_1035_);
lean_dec(v_i_1038_);
v___y_983_ = v___x_1042_;
goto v___jp_982_;
}
v___jp_1043_:
{
lean_object* v___x_1045_; 
lean_inc(v_val_962_);
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_977_, v___f_978_, v___y_1044_, v_val_962_);
switch(lean_obj_tag(v___x_1045_))
{
case 0:
{
lean_object* v_index_1046_; lean_object* v_size_1047_; lean_object* v___x_1048_; 
v_index_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_index_1046_);
lean_dec_ref_known(v___x_1045_, 3);
v_size_1047_ = lean_ctor_get(v___y_1044_, 0);
lean_inc(v_size_1047_);
v___x_1048_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1044_, v_size_1047_, v_index_1046_, v_val_962_, v_val_1035_);
lean_dec(v_index_1046_);
v___y_983_ = v___x_1048_;
goto v___jp_982_;
}
case 1:
{
lean_object* v_index_1049_; 
v_index_1049_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_index_1049_);
lean_dec_ref_known(v___x_1045_, 1);
v___y_1037_ = v___y_1044_;
v_i_1038_ = v_index_1049_;
goto v___jp_1036_;
}
default: 
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1044_, v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_index_1052_; 
v_index_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_index_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___y_1037_ = v___y_1044_;
v_i_1038_ = v_index_1052_;
goto v___jp_1036_;
}
else
{
lean_dec(v_val_1035_);
lean_dec(v_val_962_);
v___y_983_ = v___y_1044_;
goto v___jp_982_;
}
}
}
}
}
}
v___jp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 1, v___y_983_);
lean_ctor_set(v___x_975_, 0, v_entries_981_);
v___x_985_ = v___x_975_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_entries_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___y_983_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_985_);
v___x_987_ = v___x_970_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany___lam__1(lean_object* v_key_1069_, lean_object* v___f_1070_, lean_object* v___f_1071_, lean_object* v_x1_1072_, lean_object* v_x2_1073_){
_start:
{
lean_object* v_entries_1074_; lean_object* v_indexes_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1170_; 
v_entries_1074_ = lean_ctor_get(v_x1_1072_, 0);
v_indexes_1075_ = lean_ctor_get(v_x1_1072_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_x1_1072_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1077_ = v_x1_1072_;
v_isShared_1078_ = v_isSharedCheck_1170_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_indexes_1075_);
lean_inc(v_entries_1074_);
lean_dec(v_x1_1072_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1170_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_i_1079_; lean_object* v___x_1080_; lean_object* v_entries_1081_; lean_object* v___x_1082_; 
v_i_1079_ = lean_array_get_size(v_entries_1074_);
lean_inc_ref_n(v_key_1069_, 2);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v_key_1069_);
lean_ctor_set(v___x_1080_, 1, v_x2_1073_);
v_entries_1081_ = lean_array_push(v_entries_1074_, v___x_1080_);
lean_inc_ref(v___f_1071_);
lean_inc_ref(v___f_1070_);
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1070_, v___f_1071_, v_indexes_1075_, v_key_1069_);
switch(lean_obj_tag(v___x_1082_))
{
case 0:
{
lean_object* v_index_1083_; lean_object* v_value_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_val_1087_; lean_object* v_size_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_dec_ref(v___f_1071_);
lean_dec_ref(v___f_1070_);
v_index_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_index_1083_);
v_value_1084_ = lean_ctor_get(v___x_1082_, 2);
lean_inc(v_value_1084_);
lean_dec_ref_known(v___x_1082_, 3);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_value_1084_);
v___x_1086_ = l_Std_Http_Headers_insert___lam__0(v_i_1079_, v___x_1085_);
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_val_1087_);
lean_dec(v___x_1086_);
v_size_1088_ = lean_ctor_get(v_indexes_1075_, 0);
lean_inc(v_size_1088_);
v___x_1089_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1075_, v_size_1088_, v_index_1083_, v_key_1069_, v_val_1087_);
lean_dec(v_index_1083_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1089_);
lean_ctor_set(v___x_1077_, 0, v_entries_1081_);
v___x_1091_ = v___x_1077_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_entries_1081_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
case 1:
{
lean_object* v_index_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_val_1096_; lean_object* v___y_1098_; lean_object* v_i_1099_; lean_object* v_size_1119_; lean_object* v_keyArray_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_index_1093_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_index_1093_);
lean_dec_ref_known(v___x_1082_, 1);
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Std_Http_Headers_insert___lam__0(v_i_1079_, v___x_1094_);
v_val_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1096_);
lean_dec(v___x_1095_);
v_size_1119_ = lean_ctor_get(v_indexes_1075_, 0);
v_keyArray_1120_ = lean_ctor_get(v_indexes_1075_, 1);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_size_1119_, v___x_1121_);
v___x_1123_ = lean_array_get_size(v_keyArray_1120_);
v___x_1124_ = lean_nat_dec_lt(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec(v___x_1122_);
lean_dec(v_index_1093_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1125_ = lean_unsigned_to_nat(4u);
v___x_1126_ = lean_nat_mul(v___x_1122_, v___x_1125_);
v___x_1127_ = lean_unsigned_to_nat(3u);
v___x_1128_ = lean_nat_mul(v___x_1123_, v___x_1127_);
v___x_1129_ = lean_nat_dec_le(v___x_1126_, v___x_1128_);
lean_dec(v___x_1128_);
lean_dec(v___x_1126_);
if (v___x_1129_ == 0)
{
lean_dec(v___x_1122_);
lean_dec(v_index_1093_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_del_object(v___x_1077_);
lean_dec_ref(v___f_1071_);
lean_dec_ref(v___f_1070_);
v___x_1130_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1075_, v___x_1122_, v_index_1093_, v_key_1069_, v_val_1096_);
lean_dec(v_index_1093_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_entries_1081_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
return v___x_1131_;
}
}
v___jp_1097_:
{
lean_object* v_size_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v_size_1100_ = lean_ctor_get(v___y_1098_, 0);
v___x_1101_ = lean_unsigned_to_nat(1u);
v___x_1102_ = lean_nat_add(v_size_1100_, v___x_1101_);
v___x_1103_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1098_, v___x_1102_, v_i_1099_, v_key_1069_, v_val_1096_);
lean_dec(v_i_1099_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1103_);
lean_ctor_set(v___x_1077_, 0, v_entries_1081_);
v___x_1105_ = v___x_1077_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_entries_1081_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_inc_ref(v___f_1071_);
lean_inc_ref(v___f_1070_);
v___x_1108_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1070_, v___f_1071_, v_indexes_1075_);
lean_inc_ref(v_key_1069_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1070_, v___f_1071_, v___x_1108_, v_key_1069_);
switch(lean_obj_tag(v___x_1109_))
{
case 0:
{
lean_object* v_index_1110_; lean_object* v_size_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_del_object(v___x_1077_);
v_index_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_index_1110_);
lean_dec_ref_known(v___x_1109_, 3);
v_size_1111_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_size_1111_);
v___x_1112_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1108_, v_size_1111_, v_index_1110_, v_key_1069_, v_val_1096_);
lean_dec(v_index_1110_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v_entries_1081_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
return v___x_1113_;
}
case 1:
{
lean_object* v_index_1114_; 
v_index_1114_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_index_1114_);
lean_dec_ref_known(v___x_1109_, 1);
v___y_1098_ = v___x_1108_;
v_i_1099_ = v_index_1114_;
goto v___jp_1097_;
}
default: 
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1108_, v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_index_1117_; 
v_index_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_index_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___y_1098_ = v___x_1108_;
v_i_1099_ = v_index_1117_;
goto v___jp_1097_;
}
else
{
lean_object* v___x_1118_; 
lean_dec(v_val_1096_);
lean_del_object(v___x_1077_);
lean_dec_ref(v_key_1069_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_entries_1081_);
lean_ctor_set(v___x_1118_, 1, v___x_1108_);
return v___x_1118_;
}
}
}
}
}
default: 
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_val_1134_; lean_object* v___y_1136_; lean_object* v_i_1137_; lean_object* v___y_1146_; lean_object* v_size_1157_; lean_object* v_keyArray_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Std_Http_Headers_insert___lam__0(v_i_1079_, v___x_1132_);
v_val_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_val_1134_);
lean_dec(v___x_1133_);
v_size_1157_ = lean_ctor_get(v_indexes_1075_, 0);
v_keyArray_1158_ = lean_ctor_get(v_indexes_1075_, 1);
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_add(v_size_1157_, v___x_1159_);
v___x_1161_ = lean_array_get_size(v_keyArray_1158_);
v___x_1162_ = lean_nat_dec_lt(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec(v___x_1160_);
lean_inc_ref(v___f_1071_);
lean_inc_ref(v___f_1070_);
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1070_, v___f_1071_, v_indexes_1075_);
v___y_1146_ = v___x_1163_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1164_ = lean_unsigned_to_nat(4u);
v___x_1165_ = lean_nat_mul(v___x_1160_, v___x_1164_);
lean_dec(v___x_1160_);
v___x_1166_ = lean_unsigned_to_nat(3u);
v___x_1167_ = lean_nat_mul(v___x_1161_, v___x_1166_);
v___x_1168_ = lean_nat_dec_le(v___x_1165_, v___x_1167_);
lean_dec(v___x_1167_);
lean_dec(v___x_1165_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_inc_ref(v___f_1071_);
lean_inc_ref(v___f_1070_);
v___x_1169_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1070_, v___f_1071_, v_indexes_1075_);
v___y_1146_ = v___x_1169_;
goto v___jp_1145_;
}
else
{
v___y_1146_ = v_indexes_1075_;
goto v___jp_1145_;
}
}
v___jp_1135_:
{
lean_object* v_size_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v_size_1138_ = lean_ctor_get(v___y_1136_, 0);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v_size_1138_, v___x_1139_);
v___x_1141_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1136_, v___x_1140_, v_i_1137_, v_key_1069_, v_val_1134_);
lean_dec(v_i_1137_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1141_);
lean_ctor_set(v___x_1077_, 0, v_entries_1081_);
v___x_1143_ = v___x_1077_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_entries_1081_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
v___jp_1145_:
{
lean_object* v___x_1147_; 
lean_inc_ref(v_key_1069_);
v___x_1147_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1070_, v___f_1071_, v___y_1146_, v_key_1069_);
switch(lean_obj_tag(v___x_1147_))
{
case 0:
{
lean_object* v_index_1148_; lean_object* v_size_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_del_object(v___x_1077_);
v_index_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_index_1148_);
lean_dec_ref_known(v___x_1147_, 3);
v_size_1149_ = lean_ctor_get(v___y_1146_, 0);
lean_inc(v_size_1149_);
v___x_1150_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1146_, v_size_1149_, v_index_1148_, v_key_1069_, v_val_1134_);
lean_dec(v_index_1148_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_entries_1081_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
return v___x_1151_;
}
case 1:
{
lean_object* v_index_1152_; 
v_index_1152_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_index_1152_);
lean_dec_ref_known(v___x_1147_, 1);
v___y_1136_ = v___y_1146_;
v_i_1137_ = v_index_1152_;
goto v___jp_1135_;
}
default: 
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1146_, v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_index_1155_; 
v_index_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_index_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___y_1136_ = v___y_1146_;
v_i_1137_ = v_index_1155_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1156_; 
lean_dec(v_val_1134_);
lean_del_object(v___x_1077_);
lean_dec_ref(v_key_1069_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_entries_1081_);
lean_ctor_set(v___x_1156_, 1, v___y_1146_);
return v___x_1156_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_insertMany(lean_object* v_headers_1171_, lean_object* v_key_1172_, lean_object* v_values_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_array_get_size(v_values_1173_);
v___x_1176_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1177_ = lean_nat_dec_lt(v___x_1174_, v___x_1175_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_values_1173_);
lean_dec_ref(v_key_1172_);
return v_headers_1171_;
}
else
{
lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___f_1180_; uint8_t v___x_1181_; 
v___f_1178_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1179_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_1180_ = lean_alloc_closure((void*)(l_Std_Http_Headers_insertMany___lam__1), 5, 3);
lean_closure_set(v___f_1180_, 0, v_key_1172_);
lean_closure_set(v___f_1180_, 1, v___f_1178_);
lean_closure_set(v___f_1180_, 2, v___f_1179_);
v___x_1181_ = lean_nat_dec_le(v___x_1175_, v___x_1175_);
if (v___x_1181_ == 0)
{
if (v___x_1177_ == 0)
{
lean_dec_ref(v___f_1180_);
lean_dec_ref(v_values_1173_);
return v_headers_1171_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_of_nat(v___x_1175_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1176_, v___f_1180_, v_values_1173_, v___x_1182_, v___x_1183_, v_headers_1171_);
return v___x_1184_;
}
}
else
{
size_t v___x_1185_; size_t v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((size_t)0ULL);
v___x_1186_ = lean_usize_of_nat(v___x_1175_);
v___x_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1176_, v___f_1180_, v_values_1173_, v___x_1185_, v___x_1186_, v_headers_1171_);
return v___x_1187_;
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l_Std_Http_instInhabitedHeaders_default___closed__3, &l_Std_Http_instInhabitedHeaders_default___closed__3_once, _init_l_Std_Http_instInhabitedHeaders_default___closed__3);
v___x_1191_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__0));
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_object* v_00_u03b2_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1, &l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1_once, _init_l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0___closed__1);
return v___x_1194_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty___closed__0(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_1195_;
}
}
static lean_object* _init_l_Std_Http_Headers_empty(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(lean_object* v_m_1197_, lean_object* v_query_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_, lean_object* v_x_1201_){
_start:
{
lean_object* v_zero_1202_; uint8_t v_isZero_1203_; 
v_zero_1202_ = lean_unsigned_to_nat(0u);
v_isZero_1203_ = lean_nat_dec_eq(v_x_1200_, v_zero_1202_);
if (v_isZero_1203_ == 1)
{
lean_dec(v_x_1201_);
lean_dec(v_x_1200_);
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_box(2);
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_val_1205_ = lean_ctor_get(v_x_1199_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v_x_1199_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_val_1205_);
lean_dec(v_x_1199_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_val_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_keyArray_1213_; lean_object* v_valueArray_1214_; lean_object* v___x_1215_; uint8_t v_isSome_1216_; 
v_keyArray_1213_ = lean_ctor_get(v_m_1197_, 1);
v_valueArray_1214_ = lean_ctor_get(v_m_1197_, 2);
v___x_1215_ = lean_array_fget_borrowed(v_keyArray_1213_, v_x_1201_);
v_isSome_1216_ = lean_noption_is_some(v___x_1215_);
if (v_isSome_1216_ == 0)
{
lean_dec(v_x_1200_);
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1217_, 0, v_x_1201_);
return v___x_1217_;
}
else
{
lean_object* v_val_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_x_1201_);
v_val_1218_ = lean_ctor_get(v_x_1199_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1199_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v_x_1199_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_val_1218_);
lean_dec(v_x_1199_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_val_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_one_1226_; lean_object* v_n_1227_; lean_object* v___y_1229_; 
v_one_1226_ = lean_unsigned_to_nat(1u);
v_n_1227_ = lean_nat_sub(v_x_1200_, v_one_1226_);
lean_dec(v_x_1200_);
if (v_isSome_1216_ == 0)
{
goto v___jp_1235_;
}
else
{
lean_object* v___x_1237_; uint8_t v_isSome_1238_; 
v___x_1237_ = lean_array_fget_borrowed(v_valueArray_1214_, v_x_1201_);
v_isSome_1238_ = lean_noption_is_some(v___x_1237_);
if (v_isSome_1238_ == 0)
{
goto v___jp_1235_;
}
else
{
lean_object* v_val_1239_; uint8_t v___x_1240_; 
lean_inc(v___x_1215_);
v_val_1239_ = lean_noption_get(v___x_1215_);
v___x_1240_ = lean_string_dec_eq(v_val_1239_, v_query_1198_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
lean_dec(v_val_1239_);
v___x_1241_ = lean_array_get_size(v_keyArray_1213_);
v___x_1242_ = lean_nat_add(v_x_1201_, v_one_1226_);
lean_dec(v_x_1201_);
v___x_1243_ = lean_nat_dec_lt(v___x_1242_, v___x_1241_);
if (v___x_1243_ == 0)
{
lean_dec(v___x_1242_);
v_x_1200_ = v_n_1227_;
v_x_1201_ = v_zero_1202_;
goto _start;
}
else
{
v_x_1200_ = v_n_1227_;
v_x_1201_ = v___x_1242_;
goto _start;
}
}
else
{
lean_object* v_val_1246_; lean_object* v___x_1247_; 
lean_dec(v_n_1227_);
lean_dec(v_x_1199_);
lean_inc(v___x_1237_);
v_val_1246_ = lean_noption_get(v___x_1237_);
v___x_1247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1247_, 0, v_x_1201_);
lean_ctor_set(v___x_1247_, 1, v_val_1239_);
lean_ctor_set(v___x_1247_, 2, v_val_1246_);
return v___x_1247_;
}
}
}
v___jp_1228_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = lean_array_get_size(v_keyArray_1213_);
v___x_1231_ = lean_nat_add(v_x_1201_, v_one_1226_);
lean_dec(v_x_1201_);
v___x_1232_ = lean_nat_dec_lt(v___x_1231_, v___x_1230_);
if (v___x_1232_ == 0)
{
lean_dec(v___x_1231_);
v_x_1199_ = v___y_1229_;
v_x_1200_ = v_n_1227_;
v_x_1201_ = v_zero_1202_;
goto _start;
}
else
{
v_x_1199_ = v___y_1229_;
v_x_1200_ = v_n_1227_;
v_x_1201_ = v___x_1231_;
goto _start;
}
}
v___jp_1235_:
{
if (lean_obj_tag(v_x_1199_) == 0)
{
lean_object* v___x_1236_; 
lean_inc(v_x_1201_);
v___x_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_x_1201_);
v___y_1229_ = v___x_1236_;
goto v___jp_1228_;
}
else
{
v___y_1229_ = v_x_1199_;
goto v___jp_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_1248_, lean_object* v_query_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_m_1248_, v_query_1249_, v_x_1250_, v_x_1251_, v_x_1252_);
lean_dec_ref(v_query_1249_);
lean_dec_ref(v_m_1248_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(lean_object* v_m_1254_, lean_object* v_query_1255_){
_start:
{
lean_object* v_keyArray_1256_; lean_object* v___x_1257_; uint64_t v___x_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; uint64_t v_fold_1261_; uint64_t v___x_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; size_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_keyArray_1256_ = lean_ctor_get(v_m_1254_, 1);
v___x_1257_ = lean_array_get_size(v_keyArray_1256_);
v___x_1258_ = lean_string_hash(v_query_1255_);
v___x_1259_ = 32ULL;
v___x_1260_ = lean_uint64_shift_right(v___x_1258_, v___x_1259_);
v_fold_1261_ = lean_uint64_xor(v___x_1258_, v___x_1260_);
v___x_1262_ = 16ULL;
v___x_1263_ = lean_uint64_shift_right(v_fold_1261_, v___x_1262_);
v___x_1264_ = lean_uint64_xor(v_fold_1261_, v___x_1263_);
v___x_1265_ = lean_uint64_to_usize(v___x_1264_);
v___x_1266_ = lean_usize_of_nat(v___x_1257_);
v___x_1267_ = ((size_t)1ULL);
v___x_1268_ = lean_usize_sub(v___x_1266_, v___x_1267_);
v___x_1269_ = lean_usize_land(v___x_1265_, v___x_1268_);
v___x_1270_ = lean_usize_to_nat(v___x_1269_);
v___x_1271_ = lean_box(0);
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_m_1254_, v_query_1255_, v___x_1271_, v___x_1257_, v___x_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg___boxed(lean_object* v_m_1273_, lean_object* v_query_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_m_1273_, v_query_1274_);
lean_dec_ref(v_query_1274_);
lean_dec_ref(v_m_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_b_1276_, lean_object* v_acc_1277_, lean_object* v_i_1278_){
_start:
{
lean_object* v___y_1280_; lean_object* v_keyArray_1288_; lean_object* v_valueArray_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_keyArray_1288_ = lean_ctor_get(v_b_1276_, 1);
v_valueArray_1289_ = lean_ctor_get(v_b_1276_, 2);
v___x_1290_ = lean_array_get_size(v_keyArray_1288_);
v___x_1291_ = lean_nat_dec_lt(v_i_1278_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec(v_i_1278_);
return v_acc_1277_;
}
else
{
lean_object* v___x_1292_; uint8_t v_isSome_1293_; 
v___x_1292_ = lean_array_fget_borrowed(v_keyArray_1288_, v_i_1278_);
v_isSome_1293_ = lean_noption_is_some(v___x_1292_);
if (v_isSome_1293_ == 0)
{
goto v___jp_1284_;
}
else
{
lean_object* v___x_1294_; uint8_t v_isSome_1295_; 
v___x_1294_ = lean_array_fget_borrowed(v_valueArray_1289_, v_i_1278_);
v_isSome_1295_ = lean_noption_is_some(v___x_1294_);
if (v_isSome_1295_ == 0)
{
goto v___jp_1284_;
}
else
{
lean_object* v_val_1296_; lean_object* v_val_1297_; lean_object* v_i_1299_; lean_object* v___x_1304_; 
lean_inc(v___x_1292_);
v_val_1296_ = lean_noption_get(v___x_1292_);
lean_inc(v___x_1294_);
v_val_1297_ = lean_noption_get(v___x_1294_);
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_acc_1277_, v_val_1296_);
switch(lean_obj_tag(v___x_1304_))
{
case 0:
{
lean_object* v_index_1305_; lean_object* v_size_1306_; lean_object* v___x_1307_; 
v_index_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_index_1305_);
lean_dec_ref_known(v___x_1304_, 3);
v_size_1306_ = lean_ctor_get(v_acc_1277_, 0);
lean_inc(v_size_1306_);
v___x_1307_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1277_, v_size_1306_, v_index_1305_, v_val_1296_, v_val_1297_);
lean_dec(v_index_1305_);
v___y_1280_ = v___x_1307_;
goto v___jp_1279_;
}
case 1:
{
lean_object* v_index_1308_; 
v_index_1308_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_index_1308_);
lean_dec_ref_known(v___x_1304_, 1);
v_i_1299_ = v_index_1308_;
goto v___jp_1298_;
}
default: 
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1277_, v___x_1309_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_index_1311_; 
v_index_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_index_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v_i_1299_ = v_index_1311_;
goto v___jp_1298_;
}
else
{
lean_dec(v_val_1297_);
lean_dec(v_val_1296_);
v___y_1280_ = v_acc_1277_;
goto v___jp_1279_;
}
}
}
v___jp_1298_:
{
lean_object* v_size_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_size_1300_ = lean_ctor_get(v_acc_1277_, 0);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v_size_1300_, v___x_1301_);
v___x_1303_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1277_, v___x_1302_, v_i_1299_, v_val_1296_, v_val_1297_);
lean_dec(v_i_1299_);
v___y_1280_ = v___x_1303_;
goto v___jp_1279_;
}
}
}
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v_i_1278_, v___x_1281_);
lean_dec(v_i_1278_);
v_acc_1277_ = v___y_1280_;
v_i_1278_ = v___x_1282_;
goto _start;
}
v___jp_1284_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_add(v_i_1278_, v___x_1285_);
lean_dec(v_i_1278_);
v_i_1278_ = v___x_1286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_b_1312_, lean_object* v_acc_1313_, lean_object* v_i_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg(v_b_1312_, v_acc_1313_, v_i_1314_);
lean_dec_ref(v_b_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg(lean_object* v_init_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_unsigned_to_nat(0u);
v___x_1319_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg(v_b_1317_, v_init_1316_, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_init_1320_, lean_object* v_b_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg(v_init_1320_, v_b_1321_);
lean_dec_ref(v_b_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(lean_object* v_m_1323_){
_start:
{
lean_object* v_keyArray_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_cellCount_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_target_1331_; lean_object* v___x_1332_; 
v_keyArray_1324_ = lean_ctor_get(v_m_1323_, 1);
v___x_1325_ = lean_array_get_size(v_keyArray_1324_);
v___x_1326_ = lean_unsigned_to_nat(2u);
v_cellCount_1327_ = lean_nat_mul(v___x_1325_, v___x_1326_);
v___x_1328_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1327_);
v___x_1329_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1327_);
v___x_1330_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1327_);
v_target_1331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1331_, 0, v___x_1328_);
lean_ctor_set(v_target_1331_, 1, v___x_1329_);
lean_ctor_set(v_target_1331_, 2, v___x_1330_);
v___x_1332_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg(v_target_1331_, v_m_1323_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg___boxed(lean_object* v_m_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_m_1333_);
lean_dec_ref(v_m_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__2___redArg(lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
return v_x_1335_;
}
else
{
lean_object* v_head_1337_; lean_object* v_tail_1338_; lean_object* v_fst_1339_; lean_object* v_entries_1340_; lean_object* v_indexes_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1427_; 
v_head_1337_ = lean_ctor_get(v_x_1336_, 0);
lean_inc(v_head_1337_);
v_tail_1338_ = lean_ctor_get(v_x_1336_, 1);
lean_inc(v_tail_1338_);
lean_dec_ref_known(v_x_1336_, 2);
v_fst_1339_ = lean_ctor_get(v_head_1337_, 0);
lean_inc(v_fst_1339_);
v_entries_1340_ = lean_ctor_get(v_x_1335_, 0);
v_indexes_1341_ = lean_ctor_get(v_x_1335_, 1);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1335_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1343_ = v_x_1335_;
v_isShared_1344_ = v_isSharedCheck_1427_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_indexes_1341_);
lean_inc(v_entries_1340_);
lean_dec(v_x_1335_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1427_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_i_1345_; lean_object* v_entries_1346_; lean_object* v___y_1348_; lean_object* v___x_1353_; 
v_i_1345_ = lean_array_get_size(v_entries_1340_);
v_entries_1346_ = lean_array_push(v_entries_1340_, v_head_1337_);
v___x_1353_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_indexes_1341_, v_fst_1339_);
switch(lean_obj_tag(v___x_1353_))
{
case 0:
{
lean_object* v_index_1354_; lean_object* v_value_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_val_1358_; lean_object* v_size_1359_; lean_object* v___x_1360_; 
v_index_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_index_1354_);
v_value_1355_ = lean_ctor_get(v___x_1353_, 2);
lean_inc(v_value_1355_);
lean_dec_ref_known(v___x_1353_, 3);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_value_1355_);
v___x_1357_ = l_Std_Http_Headers_insert___lam__0(v_i_1345_, v___x_1356_);
v_val_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_val_1358_);
lean_dec(v___x_1357_);
v_size_1359_ = lean_ctor_get(v_indexes_1341_, 0);
lean_inc(v_size_1359_);
v___x_1360_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1341_, v_size_1359_, v_index_1354_, v_fst_1339_, v_val_1358_);
lean_dec(v_index_1354_);
v___y_1348_ = v___x_1360_;
goto v___jp_1347_;
}
case 1:
{
lean_object* v_index_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_val_1364_; lean_object* v___y_1366_; lean_object* v_i_1367_; lean_object* v_size_1382_; lean_object* v_keyArray_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_index_1361_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_index_1361_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_Http_Headers_insert___lam__0(v_i_1345_, v___x_1362_);
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec(v___x_1363_);
v_size_1382_ = lean_ctor_get(v_indexes_1341_, 0);
v_keyArray_1383_ = lean_ctor_get(v_indexes_1341_, 1);
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_add(v_size_1382_, v___x_1384_);
v___x_1386_ = lean_array_get_size(v_keyArray_1383_);
v___x_1387_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec(v___x_1385_);
lean_dec(v_index_1361_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1388_ = lean_unsigned_to_nat(4u);
v___x_1389_ = lean_nat_mul(v___x_1385_, v___x_1388_);
v___x_1390_ = lean_unsigned_to_nat(3u);
v___x_1391_ = lean_nat_mul(v___x_1386_, v___x_1390_);
v___x_1392_ = lean_nat_dec_le(v___x_1389_, v___x_1391_);
lean_dec(v___x_1391_);
lean_dec(v___x_1389_);
if (v___x_1392_ == 0)
{
lean_dec(v___x_1385_);
lean_dec(v_index_1361_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1341_, v___x_1385_, v_index_1361_, v_fst_1339_, v_val_1364_);
lean_dec(v_index_1361_);
v___y_1348_ = v___x_1393_;
goto v___jp_1347_;
}
}
v___jp_1365_:
{
lean_object* v_size_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_size_1368_ = lean_ctor_get(v___y_1366_, 0);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_size_1368_, v___x_1369_);
v___x_1371_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1366_, v___x_1370_, v_i_1367_, v_fst_1339_, v_val_1364_);
lean_dec(v_i_1367_);
v___y_1348_ = v___x_1371_;
goto v___jp_1347_;
}
v___jp_1372_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_1341_);
lean_dec_ref(v_indexes_1341_);
v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___x_1373_, v_fst_1339_);
switch(lean_obj_tag(v___x_1374_))
{
case 0:
{
lean_object* v_index_1375_; lean_object* v_size_1376_; lean_object* v___x_1377_; 
v_index_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_index_1375_);
lean_dec_ref_known(v___x_1374_, 3);
v_size_1376_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_size_1376_);
v___x_1377_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1373_, v_size_1376_, v_index_1375_, v_fst_1339_, v_val_1364_);
lean_dec(v_index_1375_);
v___y_1348_ = v___x_1377_;
goto v___jp_1347_;
}
case 1:
{
lean_object* v_index_1378_; 
v_index_1378_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_index_1378_);
lean_dec_ref_known(v___x_1374_, 1);
v___y_1366_ = v___x_1373_;
v_i_1367_ = v_index_1378_;
goto v___jp_1365_;
}
default: 
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1373_, v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_index_1381_; 
v_index_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_index_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___y_1366_ = v___x_1373_;
v_i_1367_ = v_index_1381_;
goto v___jp_1365_;
}
else
{
lean_dec(v_val_1364_);
lean_dec(v_fst_1339_);
v___y_1348_ = v___x_1373_;
goto v___jp_1347_;
}
}
}
}
}
default: 
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_val_1396_; lean_object* v___y_1398_; lean_object* v_i_1399_; lean_object* v___y_1405_; lean_object* v_size_1414_; lean_object* v_keyArray_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Std_Http_Headers_insert___lam__0(v_i_1345_, v___x_1394_);
v_val_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_val_1396_);
lean_dec(v___x_1395_);
v_size_1414_ = lean_ctor_get(v_indexes_1341_, 0);
v_keyArray_1415_ = lean_ctor_get(v_indexes_1341_, 1);
v___x_1416_ = lean_unsigned_to_nat(1u);
v___x_1417_ = lean_nat_add(v_size_1414_, v___x_1416_);
v___x_1418_ = lean_array_get_size(v_keyArray_1415_);
v___x_1419_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v___x_1417_);
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_1341_);
lean_dec_ref(v_indexes_1341_);
v___y_1405_ = v___x_1420_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1421_ = lean_unsigned_to_nat(4u);
v___x_1422_ = lean_nat_mul(v___x_1417_, v___x_1421_);
lean_dec(v___x_1417_);
v___x_1423_ = lean_unsigned_to_nat(3u);
v___x_1424_ = lean_nat_mul(v___x_1418_, v___x_1423_);
v___x_1425_ = lean_nat_dec_le(v___x_1422_, v___x_1424_);
lean_dec(v___x_1424_);
lean_dec(v___x_1422_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_1341_);
lean_dec_ref(v_indexes_1341_);
v___y_1405_ = v___x_1426_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v_indexes_1341_;
goto v___jp_1404_;
}
}
v___jp_1397_:
{
lean_object* v_size_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v_size_1400_ = lean_ctor_get(v___y_1398_, 0);
v___x_1401_ = lean_unsigned_to_nat(1u);
v___x_1402_ = lean_nat_add(v_size_1400_, v___x_1401_);
v___x_1403_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1398_, v___x_1402_, v_i_1399_, v_fst_1339_, v_val_1396_);
lean_dec(v_i_1399_);
v___y_1348_ = v___x_1403_;
goto v___jp_1347_;
}
v___jp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___y_1405_, v_fst_1339_);
switch(lean_obj_tag(v___x_1406_))
{
case 0:
{
lean_object* v_index_1407_; lean_object* v_size_1408_; lean_object* v___x_1409_; 
v_index_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_index_1407_);
lean_dec_ref_known(v___x_1406_, 3);
v_size_1408_ = lean_ctor_get(v___y_1405_, 0);
lean_inc(v_size_1408_);
v___x_1409_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1405_, v_size_1408_, v_index_1407_, v_fst_1339_, v_val_1396_);
lean_dec(v_index_1407_);
v___y_1348_ = v___x_1409_;
goto v___jp_1347_;
}
case 1:
{
lean_object* v_index_1410_; 
v_index_1410_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_index_1410_);
lean_dec_ref_known(v___x_1406_, 1);
v___y_1398_ = v___y_1405_;
v_i_1399_ = v_index_1410_;
goto v___jp_1397_;
}
default: 
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1405_, v___x_1411_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_index_1413_; 
v_index_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_index_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___y_1398_ = v___y_1405_;
v_i_1399_ = v_index_1413_;
goto v___jp_1397_;
}
else
{
lean_dec(v_val_1396_);
lean_dec(v_fst_1339_);
v___y_1348_ = v___y_1405_;
goto v___jp_1347_;
}
}
}
}
}
}
v___jp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v___y_1348_);
lean_ctor_set(v___x_1343_, 0, v_entries_1346_);
v___x_1350_ = v___x_1343_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_entries_1346_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___y_1348_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v_x_1335_ = v___x_1350_;
v_x_1336_ = v_tail_1338_;
goto _start;
}
}
}
}
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_Internal_IndexMultiMap_empty___at___00Std_Http_Headers_empty_spec__0(lean_box(0));
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(lean_object* v_pairs_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0, &l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0_once, _init_l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg___closed__0);
v___x_1431_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__2___redArg(v___x_1430_, v_pairs_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_ofList(lean_object* v_pairs_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0(lean_object* v_00_u03b2_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_pairs_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0___redArg(v_pairs_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(lean_object* v_00_u03b2_1439_, lean_object* v_m_1440_, lean_object* v_query_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_m_1440_, v_query_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1443_, lean_object* v_m_1444_, lean_object* v_query_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0(v_00_u03b2_1443_, v_m_1444_, v_query_1445_);
lean_dec_ref(v_query_1445_);
lean_dec_ref(v_m_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(lean_object* v_00_u03b2_1447_, lean_object* v_m_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_m_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1450_, lean_object* v_m_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1(v_00_u03b2_1450_, v_m_1451_);
lean_dec_ref(v_m_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__2(lean_object* v_00_u03b2_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_List_foldl___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__2___redArg(v_x_1454_, v_x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1457_, lean_object* v_m_1458_, lean_object* v_query_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___redArg(v_m_1458_, v_query_1459_, v_x_1460_, v_x_1461_, v_x_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_m_1466_, lean_object* v_query_1467_, lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0_spec__1(v_00_u03b2_1465_, v_m_1466_, v_query_1467_, v_x_1468_, v_x_1469_, v_x_1470_, v_x_1471_);
lean_dec_ref(v_query_1467_);
lean_dec_ref(v_m_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1473_, lean_object* v_init_1474_, lean_object* v_b_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___redArg(v_init_1474_, v_b_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_init_1478_, lean_object* v_b_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3(v_00_u03b2_1477_, v_init_1478_, v_b_1479_);
lean_dec_ref(v_b_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1481_, lean_object* v_b_1482_, lean_object* v_acc_1483_, lean_object* v_i_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___redArg(v_b_1482_, v_acc_1483_, v_i_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1486_, lean_object* v_b_1487_, lean_object* v_acc_1488_, lean_object* v_i_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1_spec__3_spec__4(v_00_u03b2_1486_, v_b_1487_, v_acc_1488_, v_i_1489_);
lean_dec_ref(v_b_1487_);
return v_res_1490_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_contains(lean_object* v_headers_1491_, lean_object* v_name_1492_){
_start:
{
lean_object* v_indexes_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; uint8_t v___x_1496_; 
v_indexes_1493_ = lean_ctor_get(v_headers_1491_, 1);
v___f_1494_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1495_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_1494_, v___f_1495_, v_indexes_1493_, v_name_1492_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_contains___boxed(lean_object* v_headers_1497_, lean_object* v_name_1498_){
_start:
{
uint8_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_Std_Http_Headers_contains(v_headers_1497_, v_name_1498_);
lean_dec_ref(v_headers_1497_);
v_r_1500_ = lean_box(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1(lean_object* v_name_1501_, lean_object* v___f_1502_, lean_object* v___f_1503_, lean_object* v_x1_1504_, lean_object* v_x2_1505_){
_start:
{
lean_object* v_fst_1506_; uint8_t v___x_1507_; 
v_fst_1506_ = lean_ctor_get(v_x2_1505_, 0);
lean_inc(v_fst_1506_);
v___x_1507_ = lean_string_dec_eq(v_name_1501_, v_fst_1506_);
if (v___x_1507_ == 0)
{
lean_object* v_entries_1508_; lean_object* v_indexes_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1603_; 
v_entries_1508_ = lean_ctor_get(v_x1_1504_, 0);
v_indexes_1509_ = lean_ctor_get(v_x1_1504_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x1_1504_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1511_ = v_x1_1504_;
v_isShared_1512_ = v_isSharedCheck_1603_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_indexes_1509_);
lean_inc(v_entries_1508_);
lean_dec(v_x1_1504_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1603_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_i_1513_; lean_object* v_entries_1514_; lean_object* v___x_1515_; 
v_i_1513_ = lean_array_get_size(v_entries_1508_);
v_entries_1514_ = lean_array_push(v_entries_1508_, v_x2_1505_);
lean_inc(v_fst_1506_);
lean_inc_ref(v___f_1503_);
lean_inc_ref(v___f_1502_);
v___x_1515_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1502_, v___f_1503_, v_indexes_1509_, v_fst_1506_);
switch(lean_obj_tag(v___x_1515_))
{
case 0:
{
lean_object* v_index_1516_; lean_object* v_value_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v_val_1520_; lean_object* v_size_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec_ref(v___f_1503_);
lean_dec_ref(v___f_1502_);
v_index_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_index_1516_);
v_value_1517_ = lean_ctor_get(v___x_1515_, 2);
lean_inc(v_value_1517_);
lean_dec_ref_known(v___x_1515_, 3);
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v_value_1517_);
v___x_1519_ = l_Std_Http_Headers_insert___lam__0(v_i_1513_, v___x_1518_);
v_val_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1520_);
lean_dec(v___x_1519_);
v_size_1521_ = lean_ctor_get(v_indexes_1509_, 0);
lean_inc(v_size_1521_);
v___x_1522_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1509_, v_size_1521_, v_index_1516_, v_fst_1506_, v_val_1520_);
lean_dec(v_index_1516_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1522_);
lean_ctor_set(v___x_1511_, 0, v_entries_1514_);
v___x_1524_ = v___x_1511_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_entries_1514_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
case 1:
{
lean_object* v_index_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_val_1529_; lean_object* v___y_1531_; lean_object* v_i_1532_; lean_object* v_size_1552_; lean_object* v_keyArray_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_index_1526_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_index_1526_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1527_ = lean_box(0);
v___x_1528_ = l_Std_Http_Headers_insert___lam__0(v_i_1513_, v___x_1527_);
v_val_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1529_);
lean_dec(v___x_1528_);
v_size_1552_ = lean_ctor_get(v_indexes_1509_, 0);
v_keyArray_1553_ = lean_ctor_get(v_indexes_1509_, 1);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_size_1552_, v___x_1554_);
v___x_1556_ = lean_array_get_size(v_keyArray_1553_);
v___x_1557_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec(v___x_1555_);
lean_dec(v_index_1526_);
goto v___jp_1540_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1558_ = lean_unsigned_to_nat(4u);
v___x_1559_ = lean_nat_mul(v___x_1555_, v___x_1558_);
v___x_1560_ = lean_unsigned_to_nat(3u);
v___x_1561_ = lean_nat_mul(v___x_1556_, v___x_1560_);
v___x_1562_ = lean_nat_dec_le(v___x_1559_, v___x_1561_);
lean_dec(v___x_1561_);
lean_dec(v___x_1559_);
if (v___x_1562_ == 0)
{
lean_dec(v___x_1555_);
lean_dec(v_index_1526_);
goto v___jp_1540_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_del_object(v___x_1511_);
lean_dec_ref(v___f_1503_);
lean_dec_ref(v___f_1502_);
v___x_1563_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1509_, v___x_1555_, v_index_1526_, v_fst_1506_, v_val_1529_);
lean_dec(v_index_1526_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_entries_1514_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
return v___x_1564_;
}
}
v___jp_1530_:
{
lean_object* v_size_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_size_1533_ = lean_ctor_get(v___y_1531_, 0);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v_size_1533_, v___x_1534_);
v___x_1536_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1531_, v___x_1535_, v_i_1532_, v_fst_1506_, v_val_1529_);
lean_dec(v_i_1532_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1536_);
lean_ctor_set(v___x_1511_, 0, v_entries_1514_);
v___x_1538_ = v___x_1511_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_entries_1514_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
v___jp_1540_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_inc_ref(v___f_1503_);
lean_inc_ref(v___f_1502_);
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1502_, v___f_1503_, v_indexes_1509_);
lean_inc(v_fst_1506_);
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1502_, v___f_1503_, v___x_1541_, v_fst_1506_);
switch(lean_obj_tag(v___x_1542_))
{
case 0:
{
lean_object* v_index_1543_; lean_object* v_size_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_del_object(v___x_1511_);
v_index_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_index_1543_);
lean_dec_ref_known(v___x_1542_, 3);
v_size_1544_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_size_1544_);
v___x_1545_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1541_, v_size_1544_, v_index_1543_, v_fst_1506_, v_val_1529_);
lean_dec(v_index_1543_);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_entries_1514_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
return v___x_1546_;
}
case 1:
{
lean_object* v_index_1547_; 
v_index_1547_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_index_1547_);
lean_dec_ref_known(v___x_1542_, 1);
v___y_1531_ = v___x_1541_;
v_i_1532_ = v_index_1547_;
goto v___jp_1530_;
}
default: 
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1541_, v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_index_1550_; 
v_index_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_index_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___y_1531_ = v___x_1541_;
v_i_1532_ = v_index_1550_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1551_; 
lean_dec(v_val_1529_);
lean_del_object(v___x_1511_);
lean_dec(v_fst_1506_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_entries_1514_);
lean_ctor_set(v___x_1551_, 1, v___x_1541_);
return v___x_1551_;
}
}
}
}
}
default: 
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_val_1567_; lean_object* v___y_1569_; lean_object* v_i_1570_; lean_object* v___y_1579_; lean_object* v_size_1590_; lean_object* v_keyArray_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = l_Std_Http_Headers_insert___lam__0(v_i_1513_, v___x_1565_);
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec(v___x_1566_);
v_size_1590_ = lean_ctor_get(v_indexes_1509_, 0);
v_keyArray_1591_ = lean_ctor_get(v_indexes_1509_, 1);
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = lean_nat_add(v_size_1590_, v___x_1592_);
v___x_1594_ = lean_array_get_size(v_keyArray_1591_);
v___x_1595_ = lean_nat_dec_lt(v___x_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; 
lean_dec(v___x_1593_);
lean_inc_ref(v___f_1503_);
lean_inc_ref(v___f_1502_);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1502_, v___f_1503_, v_indexes_1509_);
v___y_1579_ = v___x_1596_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1597_ = lean_unsigned_to_nat(4u);
v___x_1598_ = lean_nat_mul(v___x_1593_, v___x_1597_);
lean_dec(v___x_1593_);
v___x_1599_ = lean_unsigned_to_nat(3u);
v___x_1600_ = lean_nat_mul(v___x_1594_, v___x_1599_);
v___x_1601_ = lean_nat_dec_le(v___x_1598_, v___x_1600_);
lean_dec(v___x_1600_);
lean_dec(v___x_1598_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_inc_ref(v___f_1503_);
lean_inc_ref(v___f_1502_);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1502_, v___f_1503_, v_indexes_1509_);
v___y_1579_ = v___x_1602_;
goto v___jp_1578_;
}
else
{
v___y_1579_ = v_indexes_1509_;
goto v___jp_1578_;
}
}
v___jp_1568_:
{
lean_object* v_size_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v_size_1571_ = lean_ctor_get(v___y_1569_, 0);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_size_1571_, v___x_1572_);
v___x_1574_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1569_, v___x_1573_, v_i_1570_, v_fst_1506_, v_val_1567_);
lean_dec(v_i_1570_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1574_);
lean_ctor_set(v___x_1511_, 0, v_entries_1514_);
v___x_1576_ = v___x_1511_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_entries_1514_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
v___jp_1578_:
{
lean_object* v___x_1580_; 
lean_inc(v_fst_1506_);
v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1502_, v___f_1503_, v___y_1579_, v_fst_1506_);
switch(lean_obj_tag(v___x_1580_))
{
case 0:
{
lean_object* v_index_1581_; lean_object* v_size_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_del_object(v___x_1511_);
v_index_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_index_1581_);
lean_dec_ref_known(v___x_1580_, 3);
v_size_1582_ = lean_ctor_get(v___y_1579_, 0);
lean_inc(v_size_1582_);
v___x_1583_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1579_, v_size_1582_, v_index_1581_, v_fst_1506_, v_val_1567_);
lean_dec(v_index_1581_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_entries_1514_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
return v___x_1584_;
}
case 1:
{
lean_object* v_index_1585_; 
v_index_1585_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_index_1585_);
lean_dec_ref_known(v___x_1580_, 1);
v___y_1569_ = v___y_1579_;
v_i_1570_ = v_index_1585_;
goto v___jp_1568_;
}
default: 
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1579_, v___x_1586_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_index_1588_; 
v_index_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_index_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___y_1569_ = v___y_1579_;
v_i_1570_ = v_index_1588_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1589_; 
lean_dec(v_val_1567_);
lean_del_object(v___x_1511_);
lean_dec(v_fst_1506_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v_entries_1514_);
lean_ctor_set(v___x_1589_, 1, v___y_1579_);
return v___x_1589_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1506_);
lean_dec_ref(v_x2_1505_);
lean_dec_ref(v___f_1503_);
lean_dec_ref(v___f_1502_);
return v_x1_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase___lam__1___boxed(lean_object* v_name_1604_, lean_object* v___f_1605_, lean_object* v___f_1606_, lean_object* v_x1_1607_, lean_object* v_x2_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_Http_Headers_erase___lam__1(v_name_1604_, v___f_1605_, v___f_1606_, v_x1_1607_, v_x2_1608_);
lean_dec_ref(v_name_1604_);
return v_res_1609_;
}
}
static lean_object* _init_l_Std_Http_Headers_erase___closed__0(void){
_start:
{
lean_object* v___f_1610_; lean_object* v___f_1611_; lean_object* v___x_1612_; 
v___f_1610_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___f_1611_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___x_1612_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_1611_, v___f_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_erase(lean_object* v_headers_1613_, lean_object* v_name_1614_){
_start:
{
lean_object* v___f_1615_; lean_object* v___f_1616_; uint8_t v___x_1617_; 
v___f_1615_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1616_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_1614_);
v___x_1617_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_1615_, v___f_1616_, v_name_1614_, v_headers_1613_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v_name_1614_);
return v_headers_1613_;
}
else
{
lean_object* v_entries_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v_entries_1618_ = lean_ctor_get(v_headers_1613_, 0);
lean_inc_ref(v_entries_1618_);
lean_dec_ref(v_headers_1613_);
v___x_1619_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__0, &l_Std_Http_Headers_erase___closed__0_once, _init_l_Std_Http_Headers_erase___closed__0);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_array_get_size(v_entries_1618_);
v___x_1622_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1623_ = lean_nat_dec_lt(v___x_1620_, v___x_1621_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v_entries_1618_);
lean_dec_ref(v_name_1614_);
return v___x_1619_;
}
else
{
lean_object* v___f_1624_; uint8_t v___x_1625_; 
v___f_1624_ = lean_alloc_closure((void*)(l_Std_Http_Headers_erase___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1624_, 0, v_name_1614_);
lean_closure_set(v___f_1624_, 1, v___f_1615_);
lean_closure_set(v___f_1624_, 2, v___f_1616_);
v___x_1625_ = lean_nat_dec_le(v___x_1621_, v___x_1621_);
if (v___x_1625_ == 0)
{
if (v___x_1623_ == 0)
{
lean_dec_ref(v___f_1624_);
lean_dec_ref(v_entries_1618_);
return v___x_1619_;
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1621_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1622_, v___f_1624_, v_entries_1618_, v___x_1626_, v___x_1627_, v___x_1619_);
return v___x_1628_;
}
}
else
{
size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = lean_usize_of_nat(v___x_1621_);
v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1622_, v___f_1624_, v_entries_1618_, v___x_1629_, v___x_1630_, v___x_1619_);
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany___lam__1(lean_object* v___f_1632_, lean_object* v_names_1633_, lean_object* v___f_1634_, lean_object* v_x1_1635_, lean_object* v_x2_1636_){
_start:
{
lean_object* v_fst_1637_; uint8_t v___x_1638_; 
v_fst_1637_ = lean_ctor_get(v_x2_1636_, 0);
lean_inc_n(v_fst_1637_, 2);
lean_inc_ref(v___f_1632_);
v___x_1638_ = l_Array_contains___redArg(v___f_1632_, v_names_1633_, v_fst_1637_);
if (v___x_1638_ == 0)
{
lean_object* v_entries_1639_; lean_object* v_indexes_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1734_; 
v_entries_1639_ = lean_ctor_get(v_x1_1635_, 0);
v_indexes_1640_ = lean_ctor_get(v_x1_1635_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x1_1635_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1642_ = v_x1_1635_;
v_isShared_1643_ = v_isSharedCheck_1734_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_indexes_1640_);
lean_inc(v_entries_1639_);
lean_dec(v_x1_1635_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1734_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_i_1644_; lean_object* v_entries_1645_; lean_object* v___x_1646_; 
v_i_1644_ = lean_array_get_size(v_entries_1639_);
v_entries_1645_ = lean_array_push(v_entries_1639_, v_x2_1636_);
lean_inc(v_fst_1637_);
lean_inc_ref(v___f_1634_);
lean_inc_ref(v___f_1632_);
v___x_1646_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1632_, v___f_1634_, v_indexes_1640_, v_fst_1637_);
switch(lean_obj_tag(v___x_1646_))
{
case 0:
{
lean_object* v_index_1647_; lean_object* v_value_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_val_1651_; lean_object* v_size_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_dec_ref(v___f_1634_);
lean_dec_ref(v___f_1632_);
v_index_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_index_1647_);
v_value_1648_ = lean_ctor_get(v___x_1646_, 2);
lean_inc(v_value_1648_);
lean_dec_ref_known(v___x_1646_, 3);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_value_1648_);
v___x_1650_ = l_Std_Http_Headers_insert___lam__0(v_i_1644_, v___x_1649_);
v_val_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_val_1651_);
lean_dec(v___x_1650_);
v_size_1652_ = lean_ctor_get(v_indexes_1640_, 0);
lean_inc(v_size_1652_);
v___x_1653_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1640_, v_size_1652_, v_index_1647_, v_fst_1637_, v_val_1651_);
lean_dec(v_index_1647_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1653_);
lean_ctor_set(v___x_1642_, 0, v_entries_1645_);
v___x_1655_ = v___x_1642_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_entries_1645_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
case 1:
{
lean_object* v_index_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v_val_1660_; lean_object* v___y_1662_; lean_object* v_i_1663_; lean_object* v_size_1683_; lean_object* v_keyArray_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_index_1657_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_index_1657_);
lean_dec_ref_known(v___x_1646_, 1);
v___x_1658_ = lean_box(0);
v___x_1659_ = l_Std_Http_Headers_insert___lam__0(v_i_1644_, v___x_1658_);
v_val_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_val_1660_);
lean_dec(v___x_1659_);
v_size_1683_ = lean_ctor_get(v_indexes_1640_, 0);
v_keyArray_1684_ = lean_ctor_get(v_indexes_1640_, 1);
v___x_1685_ = lean_unsigned_to_nat(1u);
v___x_1686_ = lean_nat_add(v_size_1683_, v___x_1685_);
v___x_1687_ = lean_array_get_size(v_keyArray_1684_);
v___x_1688_ = lean_nat_dec_lt(v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec(v___x_1686_);
lean_dec(v_index_1657_);
goto v___jp_1671_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1689_ = lean_unsigned_to_nat(4u);
v___x_1690_ = lean_nat_mul(v___x_1686_, v___x_1689_);
v___x_1691_ = lean_unsigned_to_nat(3u);
v___x_1692_ = lean_nat_mul(v___x_1687_, v___x_1691_);
v___x_1693_ = lean_nat_dec_le(v___x_1690_, v___x_1692_);
lean_dec(v___x_1692_);
lean_dec(v___x_1690_);
if (v___x_1693_ == 0)
{
lean_dec(v___x_1686_);
lean_dec(v_index_1657_);
goto v___jp_1671_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_del_object(v___x_1642_);
lean_dec_ref(v___f_1634_);
lean_dec_ref(v___f_1632_);
v___x_1694_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1640_, v___x_1686_, v_index_1657_, v_fst_1637_, v_val_1660_);
lean_dec(v_index_1657_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_entries_1645_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
return v___x_1695_;
}
}
v___jp_1661_:
{
lean_object* v_size_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v_size_1664_ = lean_ctor_get(v___y_1662_, 0);
v___x_1665_ = lean_unsigned_to_nat(1u);
v___x_1666_ = lean_nat_add(v_size_1664_, v___x_1665_);
v___x_1667_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1662_, v___x_1666_, v_i_1663_, v_fst_1637_, v_val_1660_);
lean_dec(v_i_1663_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1667_);
lean_ctor_set(v___x_1642_, 0, v_entries_1645_);
v___x_1669_ = v___x_1642_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_entries_1645_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
v___jp_1671_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_inc_ref(v___f_1634_);
lean_inc_ref(v___f_1632_);
v___x_1672_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1632_, v___f_1634_, v_indexes_1640_);
lean_inc(v_fst_1637_);
v___x_1673_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1632_, v___f_1634_, v___x_1672_, v_fst_1637_);
switch(lean_obj_tag(v___x_1673_))
{
case 0:
{
lean_object* v_index_1674_; lean_object* v_size_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_del_object(v___x_1642_);
v_index_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_index_1674_);
lean_dec_ref_known(v___x_1673_, 3);
v_size_1675_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_size_1675_);
v___x_1676_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1672_, v_size_1675_, v_index_1674_, v_fst_1637_, v_val_1660_);
lean_dec(v_index_1674_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_entries_1645_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
return v___x_1677_;
}
case 1:
{
lean_object* v_index_1678_; 
v_index_1678_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_index_1678_);
lean_dec_ref_known(v___x_1673_, 1);
v___y_1662_ = v___x_1672_;
v_i_1663_ = v_index_1678_;
goto v___jp_1661_;
}
default: 
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1672_, v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_index_1681_; 
v_index_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_index_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___y_1662_ = v___x_1672_;
v_i_1663_ = v_index_1681_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1682_; 
lean_dec(v_val_1660_);
lean_del_object(v___x_1642_);
lean_dec(v_fst_1637_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_entries_1645_);
lean_ctor_set(v___x_1682_, 1, v___x_1672_);
return v___x_1682_;
}
}
}
}
}
default: 
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_val_1698_; lean_object* v___y_1700_; lean_object* v_i_1701_; lean_object* v___y_1710_; lean_object* v_size_1721_; lean_object* v_keyArray_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1696_ = lean_box(0);
v___x_1697_ = l_Std_Http_Headers_insert___lam__0(v_i_1644_, v___x_1696_);
v_val_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_val_1698_);
lean_dec(v___x_1697_);
v_size_1721_ = lean_ctor_get(v_indexes_1640_, 0);
v_keyArray_1722_ = lean_ctor_get(v_indexes_1640_, 1);
v___x_1723_ = lean_unsigned_to_nat(1u);
v___x_1724_ = lean_nat_add(v_size_1721_, v___x_1723_);
v___x_1725_ = lean_array_get_size(v_keyArray_1722_);
v___x_1726_ = lean_nat_dec_lt(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_dec(v___x_1724_);
lean_inc_ref(v___f_1634_);
lean_inc_ref(v___f_1632_);
v___x_1727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1632_, v___f_1634_, v_indexes_1640_);
v___y_1710_ = v___x_1727_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; 
v___x_1728_ = lean_unsigned_to_nat(4u);
v___x_1729_ = lean_nat_mul(v___x_1724_, v___x_1728_);
lean_dec(v___x_1724_);
v___x_1730_ = lean_unsigned_to_nat(3u);
v___x_1731_ = lean_nat_mul(v___x_1725_, v___x_1730_);
v___x_1732_ = lean_nat_dec_le(v___x_1729_, v___x_1731_);
lean_dec(v___x_1731_);
lean_dec(v___x_1729_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
lean_inc_ref(v___f_1634_);
lean_inc_ref(v___f_1632_);
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_1632_, v___f_1634_, v_indexes_1640_);
v___y_1710_ = v___x_1733_;
goto v___jp_1709_;
}
else
{
v___y_1710_ = v_indexes_1640_;
goto v___jp_1709_;
}
}
v___jp_1699_:
{
lean_object* v_size_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v_size_1702_ = lean_ctor_get(v___y_1700_, 0);
v___x_1703_ = lean_unsigned_to_nat(1u);
v___x_1704_ = lean_nat_add(v_size_1702_, v___x_1703_);
v___x_1705_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1700_, v___x_1704_, v_i_1701_, v_fst_1637_, v_val_1698_);
lean_dec(v_i_1701_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1705_);
lean_ctor_set(v___x_1642_, 0, v_entries_1645_);
v___x_1707_ = v___x_1642_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_entries_1645_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
v___jp_1709_:
{
lean_object* v___x_1711_; 
lean_inc(v_fst_1637_);
v___x_1711_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_1632_, v___f_1634_, v___y_1710_, v_fst_1637_);
switch(lean_obj_tag(v___x_1711_))
{
case 0:
{
lean_object* v_index_1712_; lean_object* v_size_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_del_object(v___x_1642_);
v_index_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_index_1712_);
lean_dec_ref_known(v___x_1711_, 3);
v_size_1713_ = lean_ctor_get(v___y_1710_, 0);
lean_inc(v_size_1713_);
v___x_1714_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1710_, v_size_1713_, v_index_1712_, v_fst_1637_, v_val_1698_);
lean_dec(v_index_1712_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_entries_1645_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
return v___x_1715_;
}
case 1:
{
lean_object* v_index_1716_; 
v_index_1716_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_index_1716_);
lean_dec_ref_known(v___x_1711_, 1);
v___y_1700_ = v___y_1710_;
v_i_1701_ = v_index_1716_;
goto v___jp_1699_;
}
default: 
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1710_, v___x_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_index_1719_; 
v_index_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_index_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___y_1700_ = v___y_1710_;
v_i_1701_ = v_index_1719_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1720_; 
lean_dec(v_val_1698_);
lean_del_object(v___x_1642_);
lean_dec(v_fst_1637_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_entries_1645_);
lean_ctor_set(v___x_1720_, 1, v___y_1710_);
return v___x_1720_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1637_);
lean_dec_ref(v_x2_1636_);
lean_dec_ref(v___f_1634_);
lean_dec_ref(v___f_1632_);
return v_x1_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_eraseMany(lean_object* v_headers_1735_, lean_object* v_names_1736_){
_start:
{
lean_object* v_entries_1737_; lean_object* v___f_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_entries_1737_ = lean_ctor_get(v_headers_1735_, 0);
lean_inc_ref(v_entries_1737_);
lean_dec_ref(v_headers_1735_);
v___f_1738_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_1739_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v___x_1740_ = lean_obj_once(&l_Std_Http_Headers_erase___closed__0, &l_Std_Http_Headers_erase___closed__0_once, _init_l_Std_Http_Headers_erase___closed__0);
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_array_get_size(v_entries_1737_);
v___x_1743_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v___x_1744_ = lean_nat_dec_lt(v___x_1741_, v___x_1742_);
if (v___x_1744_ == 0)
{
lean_dec_ref(v_entries_1737_);
lean_dec_ref(v_names_1736_);
return v___x_1740_;
}
else
{
lean_object* v___f_1745_; uint8_t v___x_1746_; 
v___f_1745_ = lean_alloc_closure((void*)(l_Std_Http_Headers_eraseMany___lam__1), 5, 3);
lean_closure_set(v___f_1745_, 0, v___f_1738_);
lean_closure_set(v___f_1745_, 1, v_names_1736_);
lean_closure_set(v___f_1745_, 2, v___f_1739_);
v___x_1746_ = lean_nat_dec_le(v___x_1742_, v___x_1742_);
if (v___x_1746_ == 0)
{
if (v___x_1744_ == 0)
{
lean_dec_ref(v___f_1745_);
lean_dec_ref(v_entries_1737_);
return v___x_1740_;
}
else
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = lean_usize_of_nat(v___x_1742_);
v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1743_, v___f_1745_, v_entries_1737_, v___x_1747_, v___x_1748_, v___x_1740_);
return v___x_1749_;
}
}
else
{
size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = lean_usize_of_nat(v___x_1742_);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1743_, v___f_1745_, v_entries_1737_, v___x_1750_, v___x_1751_, v___x_1740_);
return v___x_1752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size(lean_object* v_headers_1753_){
_start:
{
lean_object* v_entries_1754_; lean_object* v___x_1755_; 
v_entries_1754_ = lean_ctor_get(v_headers_1753_, 0);
v___x_1755_ = lean_array_get_size(v_entries_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_size___boxed(lean_object* v_headers_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Std_Http_Headers_size(v_headers_1756_);
lean_dec_ref(v_headers_1756_);
return v_res_1757_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Headers_isEmpty(lean_object* v_headers_1758_){
_start:
{
lean_object* v_entries_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_entries_1759_ = lean_ctor_get(v_headers_1758_, 0);
v___x_1760_ = lean_array_get_size(v_entries_1759_);
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_isEmpty___boxed(lean_object* v_headers_1763_){
_start:
{
uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_res_1764_ = l_Std_Http_Headers_isEmpty(v_headers_1763_);
lean_dec_ref(v_headers_1763_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(lean_object* v_i_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___x_1768_);
v___x_1770_ = lean_array_push(v___x_1769_, v_i_1766_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v_val_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1780_; 
v_val_1772_ = lean_ctor_get(v_x_1767_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_x_1767_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1774_ = v_x_1767_;
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_val_1772_);
lean_dec(v_x_1767_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1780_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_array_push(v_val_1772_, v_i_1766_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1776_);
v___x_1778_ = v___x_1774_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(lean_object* v_as_1781_, size_t v_i_1782_, size_t v_stop_1783_, lean_object* v_b_1784_){
_start:
{
uint8_t v___x_1785_; 
v___x_1785_ = lean_usize_dec_eq(v_i_1782_, v_stop_1783_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v_fst_1787_; lean_object* v_entries_1788_; lean_object* v_indexes_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1881_; 
v___x_1786_ = lean_array_uget_borrowed(v_as_1781_, v_i_1782_);
v_fst_1787_ = lean_ctor_get(v___x_1786_, 0);
v_entries_1788_ = lean_ctor_get(v_b_1784_, 0);
v_indexes_1789_ = lean_ctor_get(v_b_1784_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_b_1784_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1791_ = v_b_1784_;
v_isShared_1792_ = v_isSharedCheck_1881_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_indexes_1789_);
lean_inc(v_entries_1788_);
lean_dec(v_b_1784_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1881_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_i_1793_; lean_object* v_entries_1794_; lean_object* v___y_1796_; lean_object* v___x_1803_; 
v_i_1793_ = lean_array_get_size(v_entries_1788_);
lean_inc(v___x_1786_);
v_entries_1794_ = lean_array_push(v_entries_1788_, v___x_1786_);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_indexes_1789_, v_fst_1787_);
switch(lean_obj_tag(v___x_1803_))
{
case 0:
{
lean_object* v_index_1804_; lean_object* v_value_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_index_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_index_1804_);
v_value_1805_ = lean_ctor_get(v___x_1803_, 2);
lean_inc(v_value_1805_);
lean_dec_ref_known(v___x_1803_, 3);
v___x_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_value_1805_);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_1793_, v___x_1806_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_size_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_size_1808_ = lean_ctor_get(v_indexes_1789_, 0);
v___x_1809_ = lean_unsigned_to_nat(1u);
v___x_1810_ = lean_nat_sub(v_size_1808_, v___x_1809_);
v___x_1811_ = l_Std_DHashMap_Raw_clearCell___redArg(v_indexes_1789_, v___x_1810_, v_index_1804_);
lean_dec(v_index_1804_);
v___y_1796_ = v___x_1811_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1812_; lean_object* v_size_1813_; lean_object* v___x_1814_; 
v_val_1812_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_val_1812_);
lean_dec_ref_known(v___x_1807_, 1);
v_size_1813_ = lean_ctor_get(v_indexes_1789_, 0);
lean_inc(v_size_1813_);
lean_inc(v_fst_1787_);
v___x_1814_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1789_, v_size_1813_, v_index_1804_, v_fst_1787_, v_val_1812_);
lean_dec(v_index_1804_);
v___y_1796_ = v___x_1814_;
goto v___jp_1795_;
}
}
case 1:
{
lean_object* v_index_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_index_1815_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_index_1815_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1816_ = lean_box(0);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_1793_, v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_dec(v_index_1815_);
v___y_1796_ = v_indexes_1789_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1818_; lean_object* v___y_1820_; lean_object* v_i_1821_; lean_object* v_size_1836_; lean_object* v_keyArray_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_val_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_val_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v_size_1836_ = lean_ctor_get(v_indexes_1789_, 0);
v_keyArray_1837_ = lean_ctor_get(v_indexes_1789_, 1);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_add(v_size_1836_, v___x_1838_);
v___x_1840_ = lean_array_get_size(v_keyArray_1837_);
v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_dec(v___x_1839_);
lean_dec(v_index_1815_);
goto v___jp_1826_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1842_ = lean_unsigned_to_nat(4u);
v___x_1843_ = lean_nat_mul(v___x_1839_, v___x_1842_);
v___x_1844_ = lean_unsigned_to_nat(3u);
v___x_1845_ = lean_nat_mul(v___x_1840_, v___x_1844_);
v___x_1846_ = lean_nat_dec_le(v___x_1843_, v___x_1845_);
lean_dec(v___x_1845_);
lean_dec(v___x_1843_);
if (v___x_1846_ == 0)
{
lean_dec(v___x_1839_);
lean_dec(v_index_1815_);
goto v___jp_1826_;
}
else
{
lean_object* v___x_1847_; 
lean_inc(v_fst_1787_);
v___x_1847_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1789_, v___x_1839_, v_index_1815_, v_fst_1787_, v_val_1818_);
lean_dec(v_index_1815_);
v___y_1796_ = v___x_1847_;
goto v___jp_1795_;
}
}
v___jp_1819_:
{
lean_object* v_size_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_size_1822_ = lean_ctor_get(v___y_1820_, 0);
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = lean_nat_add(v_size_1822_, v___x_1823_);
lean_inc(v_fst_1787_);
v___x_1825_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1820_, v___x_1824_, v_i_1821_, v_fst_1787_, v_val_1818_);
lean_dec(v_i_1821_);
v___y_1796_ = v___x_1825_;
goto v___jp_1795_;
}
v___jp_1826_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_1789_);
lean_dec_ref(v_indexes_1789_);
v___x_1828_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___x_1827_, v_fst_1787_);
switch(lean_obj_tag(v___x_1828_))
{
case 0:
{
lean_object* v_index_1829_; lean_object* v_size_1830_; lean_object* v___x_1831_; 
v_index_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_index_1829_);
lean_dec_ref_known(v___x_1828_, 3);
v_size_1830_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_size_1830_);
lean_inc(v_fst_1787_);
v___x_1831_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1827_, v_size_1830_, v_index_1829_, v_fst_1787_, v_val_1818_);
lean_dec(v_index_1829_);
v___y_1796_ = v___x_1831_;
goto v___jp_1795_;
}
case 1:
{
lean_object* v_index_1832_; 
v_index_1832_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_index_1832_);
lean_dec_ref_known(v___x_1828_, 1);
v___y_1820_ = v___x_1827_;
v_i_1821_ = v_index_1832_;
goto v___jp_1819_;
}
default: 
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1827_, v___x_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_index_1835_; 
v_index_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_index_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___y_1820_ = v___x_1827_;
v_i_1821_ = v_index_1835_;
goto v___jp_1819_;
}
else
{
lean_dec(v_val_1818_);
v___y_1796_ = v___x_1827_;
goto v___jp_1795_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_1793_, v___x_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
v___y_1796_ = v_indexes_1789_;
goto v___jp_1795_;
}
else
{
lean_object* v_val_1850_; lean_object* v___y_1852_; lean_object* v_i_1853_; lean_object* v___y_1859_; lean_object* v_size_1868_; lean_object* v_keyArray_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v_val_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_val_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v_size_1868_ = lean_ctor_get(v_indexes_1789_, 0);
v_keyArray_1869_ = lean_ctor_get(v_indexes_1789_, 1);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_nat_add(v_size_1868_, v___x_1870_);
v___x_1872_ = lean_array_get_size(v_keyArray_1869_);
v___x_1873_ = lean_nat_dec_lt(v___x_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
lean_dec(v___x_1871_);
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_1789_);
lean_dec_ref(v_indexes_1789_);
v___y_1859_ = v___x_1874_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1875_ = lean_unsigned_to_nat(4u);
v___x_1876_ = lean_nat_mul(v___x_1871_, v___x_1875_);
lean_dec(v___x_1871_);
v___x_1877_ = lean_unsigned_to_nat(3u);
v___x_1878_ = lean_nat_mul(v___x_1872_, v___x_1877_);
v___x_1879_ = lean_nat_dec_le(v___x_1876_, v___x_1878_);
lean_dec(v___x_1878_);
lean_dec(v___x_1876_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_1789_);
lean_dec_ref(v_indexes_1789_);
v___y_1859_ = v___x_1880_;
goto v___jp_1858_;
}
else
{
v___y_1859_ = v_indexes_1789_;
goto v___jp_1858_;
}
}
v___jp_1851_:
{
lean_object* v_size_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_size_1854_ = lean_ctor_get(v___y_1852_, 0);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_add(v_size_1854_, v___x_1855_);
lean_inc(v_fst_1787_);
v___x_1857_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1852_, v___x_1856_, v_i_1853_, v_fst_1787_, v_val_1850_);
lean_dec(v_i_1853_);
v___y_1796_ = v___x_1857_;
goto v___jp_1795_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___y_1859_, v_fst_1787_);
switch(lean_obj_tag(v___x_1860_))
{
case 0:
{
lean_object* v_index_1861_; lean_object* v_size_1862_; lean_object* v___x_1863_; 
v_index_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_index_1861_);
lean_dec_ref_known(v___x_1860_, 3);
v_size_1862_ = lean_ctor_get(v___y_1859_, 0);
lean_inc(v_size_1862_);
lean_inc(v_fst_1787_);
v___x_1863_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1859_, v_size_1862_, v_index_1861_, v_fst_1787_, v_val_1850_);
lean_dec(v_index_1861_);
v___y_1796_ = v___x_1863_;
goto v___jp_1795_;
}
case 1:
{
lean_object* v_index_1864_; 
v_index_1864_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_index_1864_);
lean_dec_ref_known(v___x_1860_, 1);
v___y_1852_ = v___y_1859_;
v_i_1853_ = v_index_1864_;
goto v___jp_1851_;
}
default: 
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1859_, v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_index_1867_; 
v_index_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_index_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___y_1852_ = v___y_1859_;
v_i_1853_ = v_index_1867_;
goto v___jp_1851_;
}
else
{
lean_dec(v_val_1850_);
v___y_1796_ = v___y_1859_;
goto v___jp_1795_;
}
}
}
}
}
}
}
v___jp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___y_1796_);
lean_ctor_set(v___x_1791_, 0, v_entries_1794_);
v___x_1798_ = v___x_1791_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_entries_1794_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___y_1796_);
v___x_1798_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1782_, v___x_1799_);
v_i_1782_ = v___x_1800_;
v_b_1784_ = v___x_1798_;
goto _start;
}
}
}
}
else
{
return v_b_1784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___boxed(lean_object* v_as_1882_, lean_object* v_i_1883_, lean_object* v_stop_1884_, lean_object* v_b_1885_){
_start:
{
size_t v_i_boxed_1886_; size_t v_stop_boxed_1887_; lean_object* v_res_1888_; 
v_i_boxed_1886_ = lean_unbox_usize(v_i_1883_);
lean_dec(v_i_1883_);
v_stop_boxed_1887_ = lean_unbox_usize(v_stop_1884_);
lean_dec(v_stop_1884_);
v_res_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1882_, v_i_boxed_1886_, v_stop_boxed_1887_, v_b_1885_);
lean_dec_ref(v_as_1882_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(lean_object* v_m1_1889_, lean_object* v_m2_1890_){
_start:
{
lean_object* v_entries_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_entries_1891_ = lean_ctor_get(v_m2_1890_, 0);
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_array_get_size(v_entries_1891_);
v___x_1894_ = lean_nat_dec_lt(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
return v_m1_1889_;
}
else
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_nat_dec_le(v___x_1893_, v___x_1893_);
if (v___x_1895_ == 0)
{
if (v___x_1894_ == 0)
{
return v_m1_1889_;
}
else
{
size_t v___x_1896_; size_t v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = ((size_t)0ULL);
v___x_1897_ = lean_usize_of_nat(v___x_1893_);
v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1891_, v___x_1896_, v___x_1897_, v_m1_1889_);
return v___x_1898_;
}
}
else
{
size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = ((size_t)0ULL);
v___x_1900_ = lean_usize_of_nat(v___x_1893_);
v___x_1901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_entries_1891_, v___x_1899_, v___x_1900_, v_m1_1889_);
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg___boxed(lean_object* v_m1_1902_, lean_object* v_m2_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1902_, v_m2_1903_);
lean_dec_ref(v_m2_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge(lean_object* v_headers1_1905_, lean_object* v_headers2_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_headers1_1905_, v_headers2_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_merge___boxed(lean_object* v_headers1_1908_, lean_object* v_headers2_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Std_Http_Headers_merge(v_headers1_1908_, v_headers2_1909_);
lean_dec_ref(v_headers2_1909_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(lean_object* v_00_u03b2_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_, lean_object* v_m1_1914_, lean_object* v_m2_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___redArg(v_m1_1914_, v_m2_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0___boxed(lean_object* v_00_u03b2_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_m1_1920_, lean_object* v_m2_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0(v_00_u03b2_1917_, v_inst_1918_, v_inst_1919_, v_m1_1920_, v_m2_1921_);
lean_dec_ref(v_m2_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(lean_object* v_00_u03b2_1923_, lean_object* v_as_1924_, size_t v_i_1925_, size_t v_stop_1926_, lean_object* v_b_1927_){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg(v_as_1924_, v_i_1925_, v_stop_1926_, v_b_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1929_, lean_object* v_as_1930_, lean_object* v_i_1931_, lean_object* v_stop_1932_, lean_object* v_b_1933_){
_start:
{
size_t v_i_boxed_1934_; size_t v_stop_boxed_1935_; lean_object* v_res_1936_; 
v_i_boxed_1934_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_stop_boxed_1935_ = lean_unbox_usize(v_stop_1932_);
lean_dec(v_stop_1932_);
v_res_1936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0(v_00_u03b2_1929_, v_as_1930_, v_i_boxed_1934_, v_stop_boxed_1935_, v_b_1933_);
lean_dec_ref(v_as_1930_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(lean_object* v_map_1937_){
_start:
{
lean_object* v_entries_1938_; lean_object* v___x_1939_; 
v_entries_1938_ = lean_ctor_get(v_map_1937_, 0);
lean_inc_ref(v_entries_1938_);
lean_dec_ref(v_map_1937_);
v___x_1939_ = lean_array_to_list(v_entries_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0(lean_object* v_00_u03b2_1940_, lean_object* v_map_1941_){
_start:
{
lean_object* v___x_1942_; 
v___x_1942_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_map_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toList(lean_object* v_headers_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Std_Internal_IndexMultiMap_toList___at___00Std_Http_Headers_toList_spec__0___redArg(v_headers_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray(lean_object* v_headers_1945_){
_start:
{
lean_object* v_entries_1946_; 
v_entries_1946_ = lean_ctor_get(v_headers_1945_, 0);
lean_inc_ref(v_entries_1946_);
return v_entries_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_toArray___boxed(lean_object* v_headers_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Std_Http_Headers_toArray(v_headers_1947_);
lean_dec_ref(v_headers_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(lean_object* v_f_1949_, lean_object* v_as_1950_, size_t v_i_1951_, size_t v_stop_1952_, lean_object* v_b_1953_){
_start:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_usize_dec_eq(v_i_1951_, v_stop_1952_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; 
v___x_1955_ = lean_array_uget_borrowed(v_as_1950_, v_i_1951_);
v_fst_1956_ = lean_ctor_get(v___x_1955_, 0);
v_snd_1957_ = lean_ctor_get(v___x_1955_, 1);
lean_inc(v_f_1949_);
lean_inc(v_snd_1957_);
lean_inc(v_fst_1956_);
v___x_1958_ = lean_apply_3(v_f_1949_, v_b_1953_, v_fst_1956_, v_snd_1957_);
v___x_1959_ = ((size_t)1ULL);
v___x_1960_ = lean_usize_add(v_i_1951_, v___x_1959_);
v_i_1951_ = v___x_1960_;
v_b_1953_ = v___x_1958_;
goto _start;
}
else
{
lean_dec(v_f_1949_);
return v_b_1953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg___boxed(lean_object* v_f_1962_, lean_object* v_as_1963_, lean_object* v_i_1964_, lean_object* v_stop_1965_, lean_object* v_b_1966_){
_start:
{
size_t v_i_boxed_1967_; size_t v_stop_boxed_1968_; lean_object* v_res_1969_; 
v_i_boxed_1967_ = lean_unbox_usize(v_i_1964_);
lean_dec(v_i_1964_);
v_stop_boxed_1968_ = lean_unbox_usize(v_stop_1965_);
lean_dec(v_stop_1965_);
v_res_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1962_, v_as_1963_, v_i_boxed_1967_, v_stop_boxed_1968_, v_b_1966_);
lean_dec_ref(v_as_1963_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg(lean_object* v_headers_1970_, lean_object* v_init_1971_, lean_object* v_f_1972_){
_start:
{
lean_object* v_entries_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_entries_1973_ = lean_ctor_get(v_headers_1970_, 0);
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_array_get_size(v_entries_1973_);
v___x_1976_ = lean_nat_dec_lt(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_dec(v_f_1972_);
return v_init_1971_;
}
else
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_nat_dec_le(v___x_1975_, v___x_1975_);
if (v___x_1977_ == 0)
{
if (v___x_1976_ == 0)
{
lean_dec(v_f_1972_);
return v_init_1971_;
}
else
{
size_t v___x_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = lean_usize_of_nat(v___x_1975_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1972_, v_entries_1973_, v___x_1978_, v___x_1979_, v_init_1971_);
return v___x_1980_;
}
}
else
{
size_t v___x_1981_; size_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = lean_usize_of_nat(v___x_1975_);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1972_, v_entries_1973_, v___x_1981_, v___x_1982_, v_init_1971_);
return v___x_1983_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___redArg___boxed(lean_object* v_headers_1984_, lean_object* v_init_1985_, lean_object* v_f_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Std_Http_Headers_fold___redArg(v_headers_1984_, v_init_1985_, v_f_1986_);
lean_dec_ref(v_headers_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold(lean_object* v_00_u03b1_1988_, lean_object* v_headers_1989_, lean_object* v_init_1990_, lean_object* v_f_1991_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Std_Http_Headers_fold___redArg(v_headers_1989_, v_init_1990_, v_f_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_fold___boxed(lean_object* v_00_u03b1_1993_, lean_object* v_headers_1994_, lean_object* v_init_1995_, lean_object* v_f_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Std_Http_Headers_fold(v_00_u03b1_1993_, v_headers_1994_, v_init_1995_, v_f_1996_);
lean_dec_ref(v_headers_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(lean_object* v_00_u03b1_1998_, lean_object* v_f_1999_, lean_object* v_as_2000_, size_t v_i_2001_, size_t v_stop_2002_, lean_object* v_b_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___redArg(v_f_1999_, v_as_2000_, v_i_2001_, v_stop_2002_, v_b_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0___boxed(lean_object* v_00_u03b1_2005_, lean_object* v_f_2006_, lean_object* v_as_2007_, lean_object* v_i_2008_, lean_object* v_stop_2009_, lean_object* v_b_2010_){
_start:
{
size_t v_i_boxed_2011_; size_t v_stop_boxed_2012_; lean_object* v_res_2013_; 
v_i_boxed_2011_ = lean_unbox_usize(v_i_2008_);
lean_dec(v_i_2008_);
v_stop_boxed_2012_ = lean_unbox_usize(v_stop_2009_);
lean_dec(v_stop_2009_);
v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_fold_spec__0(v_00_u03b1_2005_, v_f_2006_, v_as_2007_, v_i_boxed_2011_, v_stop_boxed_2012_, v_b_2010_);
lean_dec_ref(v_as_2007_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(lean_object* v_f_2014_, size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_bs_2017_){
_start:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2018_ == 0)
{
lean_dec_ref(v_f_2014_);
return v_bs_2017_;
}
else
{
lean_object* v_v_2019_; lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2035_; 
v_v_2019_ = lean_array_uget(v_bs_2017_, v_i_2016_);
v_fst_2020_ = lean_ctor_get(v_v_2019_, 0);
v_snd_2021_ = lean_ctor_get(v_v_2019_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_v_2019_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2023_ = v_v_2019_;
v_isShared_2024_ = v_isSharedCheck_2035_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_snd_2021_);
lean_inc(v_fst_2020_);
lean_dec(v_v_2019_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2035_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v_bs_x27_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v_bs_x27_2026_ = lean_array_uset(v_bs_2017_, v_i_2016_, v___x_2025_);
lean_inc_ref(v_f_2014_);
lean_inc(v_fst_2020_);
v___x_2027_ = lean_apply_2(v_f_2014_, v_fst_2020_, v_snd_2021_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 1, v___x_2027_);
v___x_2029_ = v___x_2023_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_fst_2020_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2016_, v___x_2030_);
v___x_2032_ = lean_array_uset(v_bs_x27_2026_, v_i_2016_, v___x_2029_);
v_i_2016_ = v___x_2031_;
v_bs_2017_ = v___x_2032_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0___boxed(lean_object* v_f_2036_, lean_object* v_sz_2037_, lean_object* v_i_2038_, lean_object* v_bs_2039_){
_start:
{
size_t v_sz_boxed_2040_; size_t v_i_boxed_2041_; lean_object* v_res_2042_; 
v_sz_boxed_2040_ = lean_unbox_usize(v_sz_2037_);
lean_dec(v_sz_2037_);
v_i_boxed_2041_ = lean_unbox_usize(v_i_2038_);
lean_dec(v_i_2038_);
v_res_2042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_2036_, v_sz_boxed_2040_, v_i_boxed_2041_, v_bs_2039_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(lean_object* v_as_2043_, size_t v_i_2044_, size_t v_stop_2045_, lean_object* v_b_2046_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_eq(v_i_2044_, v_stop_2045_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v_fst_2049_; lean_object* v_entries_2050_; lean_object* v_indexes_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2143_; 
v___x_2048_ = lean_array_uget_borrowed(v_as_2043_, v_i_2044_);
v_fst_2049_ = lean_ctor_get(v___x_2048_, 0);
v_entries_2050_ = lean_ctor_get(v_b_2046_, 0);
v_indexes_2051_ = lean_ctor_get(v_b_2046_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_b_2046_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2053_ = v_b_2046_;
v_isShared_2054_ = v_isSharedCheck_2143_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_indexes_2051_);
lean_inc(v_entries_2050_);
lean_dec(v_b_2046_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2143_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_i_2055_; lean_object* v_entries_2056_; lean_object* v___y_2058_; lean_object* v___x_2065_; 
v_i_2055_ = lean_array_get_size(v_entries_2050_);
lean_inc(v___x_2048_);
v_entries_2056_ = lean_array_push(v_entries_2050_, v___x_2048_);
v___x_2065_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_indexes_2051_, v_fst_2049_);
switch(lean_obj_tag(v___x_2065_))
{
case 0:
{
lean_object* v_index_2066_; lean_object* v_value_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v_index_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_index_2066_);
v_value_2067_ = lean_ctor_get(v___x_2065_, 2);
lean_inc(v_value_2067_);
lean_dec_ref_known(v___x_2065_, 3);
v___x_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2068_, 0, v_value_2067_);
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_2055_, v___x_2068_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_size_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_size_2070_ = lean_ctor_get(v_indexes_2051_, 0);
v___x_2071_ = lean_unsigned_to_nat(1u);
v___x_2072_ = lean_nat_sub(v_size_2070_, v___x_2071_);
v___x_2073_ = l_Std_DHashMap_Raw_clearCell___redArg(v_indexes_2051_, v___x_2072_, v_index_2066_);
lean_dec(v_index_2066_);
v___y_2058_ = v___x_2073_;
goto v___jp_2057_;
}
else
{
lean_object* v_val_2074_; lean_object* v_size_2075_; lean_object* v___x_2076_; 
v_val_2074_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2074_);
lean_dec_ref_known(v___x_2069_, 1);
v_size_2075_ = lean_ctor_get(v_indexes_2051_, 0);
lean_inc(v_size_2075_);
lean_inc(v_fst_2049_);
v___x_2076_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2051_, v_size_2075_, v_index_2066_, v_fst_2049_, v_val_2074_);
lean_dec(v_index_2066_);
v___y_2058_ = v___x_2076_;
goto v___jp_2057_;
}
}
case 1:
{
lean_object* v_index_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_index_2077_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_index_2077_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2078_ = lean_box(0);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_2055_, v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_dec(v_index_2077_);
v___y_2058_ = v_indexes_2051_;
goto v___jp_2057_;
}
else
{
lean_object* v_val_2080_; lean_object* v___y_2082_; lean_object* v_i_2083_; lean_object* v_size_2098_; lean_object* v_keyArray_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_val_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v___x_2079_, 1);
v_size_2098_ = lean_ctor_get(v_indexes_2051_, 0);
v_keyArray_2099_ = lean_ctor_get(v_indexes_2051_, 1);
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = lean_nat_add(v_size_2098_, v___x_2100_);
v___x_2102_ = lean_array_get_size(v_keyArray_2099_);
v___x_2103_ = lean_nat_dec_lt(v___x_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec(v___x_2101_);
lean_dec(v_index_2077_);
goto v___jp_2088_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2104_ = lean_unsigned_to_nat(4u);
v___x_2105_ = lean_nat_mul(v___x_2101_, v___x_2104_);
v___x_2106_ = lean_unsigned_to_nat(3u);
v___x_2107_ = lean_nat_mul(v___x_2102_, v___x_2106_);
v___x_2108_ = lean_nat_dec_le(v___x_2105_, v___x_2107_);
lean_dec(v___x_2107_);
lean_dec(v___x_2105_);
if (v___x_2108_ == 0)
{
lean_dec(v___x_2101_);
lean_dec(v_index_2077_);
goto v___jp_2088_;
}
else
{
lean_object* v___x_2109_; 
lean_inc(v_fst_2049_);
v___x_2109_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2051_, v___x_2101_, v_index_2077_, v_fst_2049_, v_val_2080_);
lean_dec(v_index_2077_);
v___y_2058_ = v___x_2109_;
goto v___jp_2057_;
}
}
v___jp_2081_:
{
lean_object* v_size_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_size_2084_ = lean_ctor_get(v___y_2082_, 0);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_nat_add(v_size_2084_, v___x_2085_);
lean_inc(v_fst_2049_);
v___x_2087_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2082_, v___x_2086_, v_i_2083_, v_fst_2049_, v_val_2080_);
lean_dec(v_i_2083_);
v___y_2058_ = v___x_2087_;
goto v___jp_2057_;
}
v___jp_2088_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_2051_);
lean_dec_ref(v_indexes_2051_);
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___x_2089_, v_fst_2049_);
switch(lean_obj_tag(v___x_2090_))
{
case 0:
{
lean_object* v_index_2091_; lean_object* v_size_2092_; lean_object* v___x_2093_; 
v_index_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_index_2091_);
lean_dec_ref_known(v___x_2090_, 3);
v_size_2092_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_size_2092_);
lean_inc(v_fst_2049_);
v___x_2093_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2089_, v_size_2092_, v_index_2091_, v_fst_2049_, v_val_2080_);
lean_dec(v_index_2091_);
v___y_2058_ = v___x_2093_;
goto v___jp_2057_;
}
case 1:
{
lean_object* v_index_2094_; 
v_index_2094_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_index_2094_);
lean_dec_ref_known(v___x_2090_, 1);
v___y_2082_ = v___x_2089_;
v_i_2083_ = v_index_2094_;
goto v___jp_2081_;
}
default: 
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2089_, v___x_2095_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_index_2097_; 
v_index_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_index_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___y_2082_ = v___x_2089_;
v_i_2083_ = v_index_2097_;
goto v___jp_2081_;
}
else
{
lean_dec(v_val_2080_);
v___y_2058_ = v___x_2089_;
goto v___jp_2057_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_box(0);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_2055_, v___x_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
v___y_2058_ = v_indexes_2051_;
goto v___jp_2057_;
}
else
{
lean_object* v_val_2112_; lean_object* v___y_2114_; lean_object* v_i_2115_; lean_object* v___y_2121_; lean_object* v_size_2130_; lean_object* v_keyArray_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v_val_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_val_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v_size_2130_ = lean_ctor_get(v_indexes_2051_, 0);
v_keyArray_2131_ = lean_ctor_get(v_indexes_2051_, 1);
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = lean_nat_add(v_size_2130_, v___x_2132_);
v___x_2134_ = lean_array_get_size(v_keyArray_2131_);
v___x_2135_ = lean_nat_dec_lt(v___x_2133_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec(v___x_2133_);
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_2051_);
lean_dec_ref(v_indexes_2051_);
v___y_2121_ = v___x_2136_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2137_ = lean_unsigned_to_nat(4u);
v___x_2138_ = lean_nat_mul(v___x_2133_, v___x_2137_);
lean_dec(v___x_2133_);
v___x_2139_ = lean_unsigned_to_nat(3u);
v___x_2140_ = lean_nat_mul(v___x_2134_, v___x_2139_);
v___x_2141_ = lean_nat_dec_le(v___x_2138_, v___x_2140_);
lean_dec(v___x_2140_);
lean_dec(v___x_2138_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_2051_);
lean_dec_ref(v_indexes_2051_);
v___y_2121_ = v___x_2142_;
goto v___jp_2120_;
}
else
{
v___y_2121_ = v_indexes_2051_;
goto v___jp_2120_;
}
}
v___jp_2113_:
{
lean_object* v_size_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_size_2116_ = lean_ctor_get(v___y_2114_, 0);
v___x_2117_ = lean_unsigned_to_nat(1u);
v___x_2118_ = lean_nat_add(v_size_2116_, v___x_2117_);
lean_inc(v_fst_2049_);
v___x_2119_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2114_, v___x_2118_, v_i_2115_, v_fst_2049_, v_val_2112_);
lean_dec(v_i_2115_);
v___y_2058_ = v___x_2119_;
goto v___jp_2057_;
}
v___jp_2120_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___y_2121_, v_fst_2049_);
switch(lean_obj_tag(v___x_2122_))
{
case 0:
{
lean_object* v_index_2123_; lean_object* v_size_2124_; lean_object* v___x_2125_; 
v_index_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_index_2123_);
lean_dec_ref_known(v___x_2122_, 3);
v_size_2124_ = lean_ctor_get(v___y_2121_, 0);
lean_inc(v_size_2124_);
lean_inc(v_fst_2049_);
v___x_2125_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2121_, v_size_2124_, v_index_2123_, v_fst_2049_, v_val_2112_);
lean_dec(v_index_2123_);
v___y_2058_ = v___x_2125_;
goto v___jp_2057_;
}
case 1:
{
lean_object* v_index_2126_; 
v_index_2126_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_index_2126_);
lean_dec_ref_known(v___x_2122_, 1);
v___y_2114_ = v___y_2121_;
v_i_2115_ = v_index_2126_;
goto v___jp_2113_;
}
default: 
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2121_, v___x_2127_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_index_2129_; 
v_index_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_index_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___y_2114_ = v___y_2121_;
v_i_2115_ = v_index_2129_;
goto v___jp_2113_;
}
else
{
lean_dec(v_val_2112_);
v___y_2058_ = v___y_2121_;
goto v___jp_2057_;
}
}
}
}
}
}
}
v___jp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___y_2058_);
lean_ctor_set(v___x_2053_, 0, v_entries_2056_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_entries_2056_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v___y_2058_);
v___x_2060_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
size_t v___x_2061_; size_t v___x_2062_; 
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2044_, v___x_2061_);
v_i_2044_ = v___x_2062_;
v_b_2046_ = v___x_2060_;
goto _start;
}
}
}
}
else
{
return v_b_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1___boxed(lean_object* v_as_2144_, lean_object* v_i_2145_, lean_object* v_stop_2146_, lean_object* v_b_2147_){
_start:
{
size_t v_i_boxed_2148_; size_t v_stop_boxed_2149_; lean_object* v_res_2150_; 
v_i_boxed_2148_ = lean_unbox_usize(v_i_2145_);
lean_dec(v_i_2145_);
v_stop_boxed_2149_ = lean_unbox_usize(v_stop_2146_);
lean_dec(v_stop_2146_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_as_2144_, v_i_boxed_2148_, v_stop_boxed_2149_, v_b_2147_);
lean_dec_ref(v_as_2144_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_mapValues(lean_object* v_headers_2151_, lean_object* v_f_2152_){
_start:
{
lean_object* v_entries_2153_; size_t v_sz_2154_; size_t v___x_2155_; lean_object* v_pairs_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v_entries_2153_ = lean_ctor_get(v_headers_2151_, 0);
lean_inc_ref(v_entries_2153_);
lean_dec_ref(v_headers_2151_);
v_sz_2154_ = lean_array_size(v_entries_2153_);
v___x_2155_ = ((size_t)0ULL);
v_pairs_2156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Http_Headers_mapValues_spec__0(v_f_2152_, v_sz_2154_, v___x_2155_, v_entries_2153_);
v___x_2157_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = lean_array_get_size(v_pairs_2156_);
v___x_2160_ = lean_nat_dec_lt(v___x_2158_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_dec_ref(v_pairs_2156_);
return v___x_2157_;
}
else
{
uint8_t v___x_2161_; 
v___x_2161_ = lean_nat_dec_le(v___x_2159_, v___x_2159_);
if (v___x_2161_ == 0)
{
if (v___x_2160_ == 0)
{
lean_dec_ref(v_pairs_2156_);
return v___x_2157_;
}
else
{
size_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_usize_of_nat(v___x_2159_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_2156_, v___x_2155_, v___x_2162_, v___x_2157_);
lean_dec_ref(v_pairs_2156_);
return v___x_2163_;
}
}
else
{
size_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_usize_of_nat(v___x_2159_);
v___x_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_2156_, v___x_2155_, v___x_2164_, v___x_2157_);
lean_dec_ref(v_pairs_2156_);
return v___x_2165_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(lean_object* v_f_2166_, lean_object* v_as_2167_, size_t v_i_2168_, size_t v_stop_2169_, lean_object* v_b_2170_){
_start:
{
lean_object* v___y_2172_; uint8_t v___x_2176_; 
v___x_2176_ = lean_usize_dec_eq(v_i_2168_, v_stop_2169_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2189_; 
v___x_2177_ = lean_array_uget(v_as_2167_, v_i_2168_);
v_fst_2178_ = lean_ctor_get(v___x_2177_, 0);
v_snd_2179_ = lean_ctor_get(v___x_2177_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2181_ = v___x_2177_;
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v___x_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; 
lean_inc_ref(v_f_2166_);
lean_inc(v_fst_2178_);
v___x_2183_ = lean_apply_2(v_f_2166_, v_fst_2178_, v_snd_2179_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_del_object(v___x_2181_);
lean_dec(v_fst_2178_);
v___y_2172_ = v_b_2170_;
goto v___jp_2171_;
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2186_; 
v_val_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v___x_2183_, 1);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v_val_2184_);
v___x_2186_ = v___x_2181_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_fst_2178_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_val_2184_);
v___x_2186_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_array_push(v_b_2170_, v___x_2186_);
v___y_2172_ = v___x_2187_;
goto v___jp_2171_;
}
}
}
}
else
{
lean_dec_ref(v_f_2166_);
return v_b_2170_;
}
v___jp_2171_:
{
size_t v___x_2173_; size_t v___x_2174_; 
v___x_2173_ = ((size_t)1ULL);
v___x_2174_ = lean_usize_add(v_i_2168_, v___x_2173_);
v_i_2168_ = v___x_2174_;
v_b_2170_ = v___y_2172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0___boxed(lean_object* v_f_2190_, lean_object* v_as_2191_, lean_object* v_i_2192_, lean_object* v_stop_2193_, lean_object* v_b_2194_){
_start:
{
size_t v_i_boxed_2195_; size_t v_stop_boxed_2196_; lean_object* v_res_2197_; 
v_i_boxed_2195_ = lean_unbox_usize(v_i_2192_);
lean_dec(v_i_2192_);
v_stop_boxed_2196_ = lean_unbox_usize(v_stop_2193_);
lean_dec(v_stop_2193_);
v_res_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_2190_, v_as_2191_, v_i_boxed_2195_, v_stop_boxed_2196_, v_b_2194_);
lean_dec_ref(v_as_2191_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(lean_object* v_f_2198_, lean_object* v_as_2199_, lean_object* v_start_2200_, lean_object* v_stop_2201_){
_start:
{
lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Std_Http_instInhabitedHeaders_default___closed__0));
v___x_2203_ = lean_nat_dec_lt(v_start_2200_, v_stop_2201_);
if (v___x_2203_ == 0)
{
lean_dec_ref(v_f_2198_);
return v___x_2202_;
}
else
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = lean_array_get_size(v_as_2199_);
v___x_2205_ = lean_nat_dec_le(v_stop_2201_, v___x_2204_);
if (v___x_2205_ == 0)
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_nat_dec_lt(v_start_2200_, v___x_2204_);
if (v___x_2206_ == 0)
{
lean_dec_ref(v_f_2198_);
return v___x_2202_;
}
else
{
size_t v___x_2207_; size_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_usize_of_nat(v_start_2200_);
v___x_2208_ = lean_usize_of_nat(v___x_2204_);
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_2198_, v_as_2199_, v___x_2207_, v___x_2208_, v___x_2202_);
return v___x_2209_;
}
}
else
{
size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_usize_of_nat(v_start_2200_);
v___x_2211_ = lean_usize_of_nat(v_stop_2201_);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0_spec__0(v_f_2198_, v_as_2199_, v___x_2210_, v___x_2211_, v___x_2202_);
return v___x_2212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0___boxed(lean_object* v_f_2213_, lean_object* v_as_2214_, lean_object* v_start_2215_, lean_object* v_stop_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_2213_, v_as_2214_, v_start_2215_, v_stop_2216_);
lean_dec(v_stop_2216_);
lean_dec(v_start_2215_);
lean_dec_ref(v_as_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap(lean_object* v_headers_2218_, lean_object* v_f_2219_){
_start:
{
lean_object* v_entries_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_pairs_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_entries_2220_ = lean_ctor_get(v_headers_2218_, 0);
v___x_2221_ = lean_unsigned_to_nat(0u);
v___x_2222_ = lean_array_get_size(v_entries_2220_);
v_pairs_2223_ = l_Array_filterMapM___at___00Std_Http_Headers_filterMap_spec__0(v_f_2219_, v_entries_2220_, v___x_2221_, v___x_2222_);
v___x_2224_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_2225_ = lean_array_get_size(v_pairs_2223_);
v___x_2226_ = lean_nat_dec_lt(v___x_2221_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_dec_ref(v_pairs_2223_);
return v___x_2224_;
}
else
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_nat_dec_le(v___x_2225_, v___x_2225_);
if (v___x_2227_ == 0)
{
if (v___x_2226_ == 0)
{
lean_dec_ref(v_pairs_2223_);
return v___x_2224_;
}
else
{
size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = lean_usize_of_nat(v___x_2225_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_2223_, v___x_2228_, v___x_2229_, v___x_2224_);
lean_dec_ref(v_pairs_2223_);
return v___x_2230_;
}
}
else
{
size_t v___x_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = lean_usize_of_nat(v___x_2225_);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_mapValues_spec__1(v_pairs_2223_, v___x_2231_, v___x_2232_, v___x_2224_);
lean_dec_ref(v_pairs_2223_);
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filterMap___boxed(lean_object* v_headers_2234_, lean_object* v_f_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_Http_Headers_filterMap(v_headers_2234_, v_f_2235_);
lean_dec_ref(v_headers_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___lam__0(lean_object* v_f_2237_, lean_object* v_k_2238_, lean_object* v_v_2239_){
_start:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
lean_inc_ref(v_v_2239_);
v___x_2240_ = lean_apply_2(v_f_2237_, v_k_2238_, v_v_2239_);
v___x_2241_ = lean_unbox(v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec_ref(v_v_2239_);
v___x_2242_ = lean_box(0);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_v_2239_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter(lean_object* v_headers_2244_, lean_object* v_f_2245_){
_start:
{
lean_object* v___f_2246_; lean_object* v___x_2247_; 
v___f_2246_ = lean_alloc_closure((void*)(l_Std_Http_Headers_filter___lam__0), 3, 1);
lean_closure_set(v___f_2246_, 0, v_f_2245_);
v___x_2247_ = l_Std_Http_Headers_filterMap(v_headers_2244_, v___f_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_filter___boxed(lean_object* v_headers_2248_, lean_object* v_f_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Std_Http_Headers_filter(v_headers_2248_, v_f_2249_);
lean_dec_ref(v_headers_2248_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(lean_object* v_name_2251_, lean_object* v_f_2252_, lean_object* v_as_2253_, size_t v_i_2254_, size_t v_stop_2255_, lean_object* v_b_2256_){
_start:
{
lean_object* v___y_2258_; lean_object* v___y_2259_; uint8_t v___x_2264_; 
v___x_2264_ = lean_usize_dec_eq(v_i_2254_, v_stop_2255_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v_fst_2266_; lean_object* v_snd_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2369_; 
v___x_2265_ = lean_array_uget(v_as_2253_, v_i_2254_);
v_fst_2266_ = lean_ctor_get(v___x_2265_, 0);
v_snd_2267_ = lean_ctor_get(v___x_2265_, 1);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2269_ = v___x_2265_;
v_isShared_2270_ = v_isSharedCheck_2369_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_snd_2267_);
lean_inc(v_fst_2266_);
lean_dec(v___x_2265_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2369_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v_i_2275_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v_i_2296_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2315_; uint8_t v___x_2367_; 
v___x_2367_ = lean_string_dec_eq(v_fst_2266_, v_name_2251_);
if (v___x_2367_ == 0)
{
v___y_2315_ = v_snd_2267_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2368_; 
lean_inc_ref(v_f_2252_);
v___x_2368_ = lean_apply_1(v_f_2252_, v_snd_2267_);
v___y_2315_ = v___x_2368_;
goto v___jp_2314_;
}
v___jp_2271_:
{
lean_object* v_size_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_size_2276_ = lean_ctor_get(v___y_2272_, 0);
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_add(v_size_2276_, v___x_2277_);
v___x_2279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2272_, v___x_2278_, v_i_2275_, v_fst_2266_, v___y_2273_);
lean_dec(v_i_2275_);
v___y_2258_ = v___y_2274_;
v___y_2259_ = v___x_2279_;
goto v___jp_2257_;
}
v___jp_2280_:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___y_2283_, v_fst_2266_);
switch(lean_obj_tag(v___x_2284_))
{
case 0:
{
lean_object* v_index_2285_; lean_object* v_size_2286_; lean_object* v___x_2287_; 
v_index_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_index_2285_);
lean_dec_ref_known(v___x_2284_, 3);
v_size_2286_ = lean_ctor_get(v___y_2283_, 0);
lean_inc(v_size_2286_);
v___x_2287_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2283_, v_size_2286_, v_index_2285_, v_fst_2266_, v___y_2281_);
lean_dec(v_index_2285_);
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___x_2287_;
goto v___jp_2257_;
}
case 1:
{
lean_object* v_index_2288_; 
v_index_2288_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_index_2288_);
lean_dec_ref_known(v___x_2284_, 1);
v___y_2272_ = v___y_2283_;
v___y_2273_ = v___y_2281_;
v___y_2274_ = v___y_2282_;
v_i_2275_ = v_index_2288_;
goto v___jp_2271_;
}
default: 
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_unsigned_to_nat(0u);
v___x_2290_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2283_, v___x_2289_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_index_2291_; 
v_index_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_index_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___y_2272_ = v___y_2283_;
v___y_2273_ = v___y_2281_;
v___y_2274_ = v___y_2282_;
v_i_2275_ = v_index_2291_;
goto v___jp_2271_;
}
else
{
lean_dec_ref(v___y_2281_);
lean_dec(v_fst_2266_);
v___y_2258_ = v___y_2282_;
v___y_2259_ = v___y_2283_;
goto v___jp_2257_;
}
}
}
}
v___jp_2292_:
{
lean_object* v_size_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_size_2297_ = lean_ctor_get(v___y_2293_, 0);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_add(v_size_2297_, v___x_2298_);
v___x_2300_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2293_, v___x_2299_, v_i_2296_, v_fst_2266_, v___y_2294_);
lean_dec(v_i_2296_);
v___y_2258_ = v___y_2295_;
v___y_2259_ = v___x_2300_;
goto v___jp_2257_;
}
v___jp_2301_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v___y_2303_);
lean_dec_ref(v___y_2303_);
v___x_2306_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v___x_2305_, v_fst_2266_);
switch(lean_obj_tag(v___x_2306_))
{
case 0:
{
lean_object* v_index_2307_; lean_object* v_size_2308_; lean_object* v___x_2309_; 
v_index_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_index_2307_);
lean_dec_ref_known(v___x_2306_, 3);
v_size_2308_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_size_2308_);
v___x_2309_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2305_, v_size_2308_, v_index_2307_, v_fst_2266_, v___y_2302_);
lean_dec(v_index_2307_);
v___y_2258_ = v___y_2304_;
v___y_2259_ = v___x_2309_;
goto v___jp_2257_;
}
case 1:
{
lean_object* v_index_2310_; 
v_index_2310_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_index_2310_);
lean_dec_ref_known(v___x_2306_, 1);
v___y_2293_ = v___x_2305_;
v___y_2294_ = v___y_2302_;
v___y_2295_ = v___y_2304_;
v_i_2296_ = v_index_2310_;
goto v___jp_2292_;
}
default: 
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2305_, v___x_2311_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_index_2313_; 
v_index_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_index_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v___y_2293_ = v___x_2305_;
v___y_2294_ = v___y_2302_;
v___y_2295_ = v___y_2304_;
v_i_2296_ = v_index_2313_;
goto v___jp_2292_;
}
else
{
lean_dec_ref(v___y_2302_);
lean_dec(v_fst_2266_);
v___y_2258_ = v___y_2304_;
v___y_2259_ = v___x_2305_;
goto v___jp_2257_;
}
}
}
}
v___jp_2314_:
{
lean_object* v_entries_2316_; lean_object* v_indexes_2317_; lean_object* v_i_2318_; lean_object* v___x_2320_; 
v_entries_2316_ = lean_ctor_get(v_b_2256_, 0);
lean_inc_ref(v_entries_2316_);
v_indexes_2317_ = lean_ctor_get(v_b_2256_, 1);
lean_inc_ref(v_indexes_2317_);
lean_dec_ref(v_b_2256_);
v_i_2318_ = lean_array_get_size(v_entries_2316_);
lean_inc(v_fst_2266_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 1, v___y_2315_);
v___x_2320_ = v___x_2269_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_fst_2266_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v___y_2315_);
v___x_2320_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v_entries_2321_; lean_object* v___x_2322_; 
v_entries_2321_ = lean_array_push(v_entries_2316_, v___x_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__0___redArg(v_indexes_2317_, v_fst_2266_);
switch(lean_obj_tag(v___x_2322_))
{
case 0:
{
lean_object* v_index_2323_; lean_object* v_value_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_index_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_index_2323_);
v_value_2324_ = lean_ctor_get(v___x_2322_, 2);
lean_inc(v_value_2324_);
lean_dec_ref_known(v___x_2322_, 3);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_value_2324_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_2318_, v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_size_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_dec(v_fst_2266_);
v_size_2327_ = lean_ctor_get(v_indexes_2317_, 0);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_nat_sub(v_size_2327_, v___x_2328_);
v___x_2330_ = l_Std_DHashMap_Raw_clearCell___redArg(v_indexes_2317_, v___x_2329_, v_index_2323_);
lean_dec(v_index_2323_);
v___y_2258_ = v_entries_2321_;
v___y_2259_ = v___x_2330_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2331_; lean_object* v_size_2332_; lean_object* v___x_2333_; 
v_val_2331_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_val_2331_);
lean_dec_ref_known(v___x_2326_, 1);
v_size_2332_ = lean_ctor_get(v_indexes_2317_, 0);
lean_inc(v_size_2332_);
v___x_2333_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2317_, v_size_2332_, v_index_2323_, v_fst_2266_, v_val_2331_);
lean_dec(v_index_2323_);
v___y_2258_ = v_entries_2321_;
v___y_2259_ = v___x_2333_;
goto v___jp_2257_;
}
}
case 1:
{
lean_object* v_index_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_index_2334_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_index_2334_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2335_ = lean_box(0);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_2318_, v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_dec(v_index_2334_);
lean_dec(v_fst_2266_);
v___y_2258_ = v_entries_2321_;
v___y_2259_ = v_indexes_2317_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2337_; lean_object* v_size_2338_; lean_object* v_keyArray_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_val_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v_size_2338_ = lean_ctor_get(v_indexes_2317_, 0);
v_keyArray_2339_ = lean_ctor_get(v_indexes_2317_, 1);
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = lean_nat_add(v_size_2338_, v___x_2340_);
v___x_2342_ = lean_array_get_size(v_keyArray_2339_);
v___x_2343_ = lean_nat_dec_lt(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec(v___x_2341_);
lean_dec(v_index_2334_);
v___y_2302_ = v_val_2337_;
v___y_2303_ = v_indexes_2317_;
v___y_2304_ = v_entries_2321_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2344_ = lean_unsigned_to_nat(4u);
v___x_2345_ = lean_nat_mul(v___x_2341_, v___x_2344_);
v___x_2346_ = lean_unsigned_to_nat(3u);
v___x_2347_ = lean_nat_mul(v___x_2342_, v___x_2346_);
v___x_2348_ = lean_nat_dec_le(v___x_2345_, v___x_2347_);
lean_dec(v___x_2347_);
lean_dec(v___x_2345_);
if (v___x_2348_ == 0)
{
lean_dec(v___x_2341_);
lean_dec(v_index_2334_);
v___y_2302_ = v_val_2337_;
v___y_2303_ = v_indexes_2317_;
v___y_2304_ = v_entries_2321_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2317_, v___x_2341_, v_index_2334_, v_fst_2266_, v_val_2337_);
lean_dec(v_index_2334_);
v___y_2258_ = v_entries_2321_;
v___y_2259_ = v___x_2349_;
goto v___jp_2257_;
}
}
}
}
default: 
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Internal_IndexMultiMap_merge___at___00Std_Http_Headers_merge_spec__0_spec__0___redArg___lam__0(v_i_2318_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_dec(v_fst_2266_);
v___y_2258_ = v_entries_2321_;
v___y_2259_ = v_indexes_2317_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2352_; lean_object* v_size_2353_; lean_object* v_keyArray_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v_val_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_size_2353_ = lean_ctor_get(v_indexes_2317_, 0);
v_keyArray_2354_ = lean_ctor_get(v_indexes_2317_, 1);
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_nat_add(v_size_2353_, v___x_2355_);
v___x_2357_ = lean_array_get_size(v_keyArray_2354_);
v___x_2358_ = lean_nat_dec_lt(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; 
lean_dec(v___x_2356_);
v___x_2359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_2317_);
lean_dec_ref(v_indexes_2317_);
v___y_2281_ = v_val_2352_;
v___y_2282_ = v_entries_2321_;
v___y_2283_ = v___x_2359_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2360_ = lean_unsigned_to_nat(4u);
v___x_2361_ = lean_nat_mul(v___x_2356_, v___x_2360_);
lean_dec(v___x_2356_);
v___x_2362_ = lean_unsigned_to_nat(3u);
v___x_2363_ = lean_nat_mul(v___x_2357_, v___x_2362_);
v___x_2364_ = lean_nat_dec_le(v___x_2361_, v___x_2363_);
lean_dec(v___x_2363_);
lean_dec(v___x_2361_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_Internal_IndexMultiMap_ofList___at___00Std_Http_Headers_ofList_spec__0_spec__1___redArg(v_indexes_2317_);
lean_dec_ref(v_indexes_2317_);
v___y_2281_ = v_val_2352_;
v___y_2282_ = v_entries_2321_;
v___y_2283_ = v___x_2365_;
goto v___jp_2280_;
}
else
{
v___y_2281_ = v_val_2352_;
v___y_2282_ = v_entries_2321_;
v___y_2283_ = v_indexes_2317_;
goto v___jp_2280_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_f_2252_);
return v_b_2256_;
}
v___jp_2257_:
{
lean_object* v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; 
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2258_);
lean_ctor_set(v___x_2260_, 1, v___y_2259_);
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2254_, v___x_2261_);
v_i_2254_ = v___x_2262_;
v_b_2256_ = v___x_2260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0___boxed(lean_object* v_name_2370_, lean_object* v_f_2371_, lean_object* v_as_2372_, lean_object* v_i_2373_, lean_object* v_stop_2374_, lean_object* v_b_2375_){
_start:
{
size_t v_i_boxed_2376_; size_t v_stop_boxed_2377_; lean_object* v_res_2378_; 
v_i_boxed_2376_ = lean_unbox_usize(v_i_2373_);
lean_dec(v_i_2373_);
v_stop_boxed_2377_ = lean_unbox_usize(v_stop_2374_);
lean_dec(v_stop_2374_);
v_res_2378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_2370_, v_f_2371_, v_as_2372_, v_i_boxed_2376_, v_stop_boxed_2377_, v_b_2375_);
lean_dec_ref(v_as_2372_);
lean_dec_ref(v_name_2370_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update(lean_object* v_headers_2379_, lean_object* v_name_2380_, lean_object* v_f_2381_){
_start:
{
lean_object* v___f_2382_; lean_object* v___f_2383_; uint8_t v___x_2384_; 
v___f_2382_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_2383_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_2380_);
v___x_2384_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_2382_, v___f_2383_, v_name_2380_, v_headers_2379_);
if (v___x_2384_ == 0)
{
lean_dec_ref(v_f_2381_);
lean_dec_ref(v_name_2380_);
lean_inc_ref(v_headers_2379_);
return v_headers_2379_;
}
else
{
lean_object* v_entries_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v_entries_2385_ = lean_ctor_get(v_headers_2379_, 0);
v___x_2386_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_array_get_size(v_entries_2385_);
v___x_2389_ = lean_nat_dec_lt(v___x_2387_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_dec_ref(v_f_2381_);
lean_dec_ref(v_name_2380_);
return v___x_2386_;
}
else
{
uint8_t v___x_2390_; 
v___x_2390_ = lean_nat_dec_le(v___x_2388_, v___x_2388_);
if (v___x_2390_ == 0)
{
if (v___x_2389_ == 0)
{
lean_dec_ref(v_f_2381_);
lean_dec_ref(v_name_2380_);
return v___x_2386_;
}
else
{
size_t v___x_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = lean_usize_of_nat(v___x_2388_);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_2380_, v_f_2381_, v_entries_2385_, v___x_2391_, v___x_2392_, v___x_2386_);
lean_dec_ref(v_name_2380_);
return v___x_2393_;
}
}
else
{
size_t v___x_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = ((size_t)0ULL);
v___x_2395_ = lean_usize_of_nat(v___x_2388_);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Headers_update_spec__0(v_name_2380_, v_f_2381_, v_entries_2385_, v___x_2394_, v___x_2395_, v___x_2386_);
lean_dec_ref(v_name_2380_);
return v___x_2396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_update___boxed(lean_object* v_headers_2397_, lean_object* v_name_2398_, lean_object* v_f_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Std_Http_Headers_update(v_headers_2397_, v_name_2398_, v_f_2399_);
lean_dec_ref(v_headers_2397_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_replaceLast(lean_object* v_headers_2401_, lean_object* v_name_2402_, lean_object* v_value_2403_){
_start:
{
lean_object* v___f_2404_; lean_object* v___f_2405_; uint8_t v___x_2406_; 
v___f_2404_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_2405_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
lean_inc_ref(v_name_2402_);
v___x_2406_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_2404_, v___f_2405_, v_name_2402_, v_headers_2401_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v_value_2403_);
lean_dec_ref(v_name_2402_);
return v_headers_2401_;
}
else
{
lean_object* v_entries_2407_; lean_object* v_indexes_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2423_; 
v_entries_2407_ = lean_ctor_get(v_headers_2401_, 0);
v_indexes_2408_ = lean_ctor_get(v_headers_2401_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_headers_2401_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2410_ = v_headers_2401_;
v_isShared_2411_ = v_isSharedCheck_2423_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_indexes_2408_);
lean_inc(v_entries_2407_);
lean_dec(v_headers_2401_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2423_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v_val_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_lastIdx_2417_; lean_object* v___x_2418_; lean_object* v_entries_2419_; lean_object* v___x_2421_; 
lean_inc_ref(v_name_2402_);
v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_2404_, v___f_2405_, v_indexes_2408_, v_name_2402_);
v_val_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_val_2413_);
lean_dec(v___x_2412_);
v___x_2414_ = lean_array_get_size(v_val_2413_);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_nat_sub(v___x_2414_, v___x_2415_);
v_lastIdx_2417_ = lean_array_fget(v_val_2413_, v___x_2416_);
lean_dec(v___x_2416_);
lean_dec(v_val_2413_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v_name_2402_);
lean_ctor_set(v___x_2418_, 1, v_value_2403_);
v_entries_2419_ = lean_array_fset(v_entries_2407_, v_lastIdx_2417_, v___x_2418_);
lean_dec(v_lastIdx_2417_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v_entries_2419_);
v___x_2421_ = v___x_2410_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_entries_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_indexes_2408_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0(lean_object* v___x_2424_, lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v_fst_2427_, lean_object* v___x_2428_, uint32_t v___x_2429_, lean_object* v___x_2430_, lean_object* v_it_2431_, lean_object* v_acc_2432_, lean_object* v_hP_2433_, lean_object* v_recur_2434_){
_start:
{
lean_object* v_it_2436_; lean_object* v_out_2437_; lean_object* v_it_2453_; lean_object* v_startInclusive_2454_; lean_object* v_endExclusive_2455_; 
if (lean_obj_tag(v_it_2431_) == 0)
{
lean_object* v_currPos_2467_; lean_object* v_searcher_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2490_; 
v_currPos_2467_ = lean_ctor_get(v_it_2431_, 0);
v_searcher_2468_ = lean_ctor_get(v_it_2431_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_it_2431_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2470_ = v_it_2431_;
v_isShared_2471_ = v_isSharedCheck_2490_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_searcher_2468_);
lean_inc(v_currPos_2467_);
lean_dec(v_it_2431_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2490_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_nat_dec_eq(v_searcher_2468_, v___x_2428_);
if (v___x_2472_ == 0)
{
uint32_t v___x_2473_; uint8_t v___x_2474_; 
lean_dec(v___x_2428_);
v___x_2473_ = lean_string_utf8_get_fast(v_fst_2427_, v_searcher_2468_);
v___x_2474_ = lean_uint32_dec_eq(v___x_2473_, v___x_2429_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_string_utf8_next_fast(v_fst_2427_, v_searcher_2468_);
lean_dec(v_searcher_2468_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2475_);
v___x_2477_ = v___x_2470_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_currPos_2467_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_apply_4(v_recur_2434_, v___x_2477_, v_acc_2432_, lean_box(0), lean_box(0));
return v___x_2478_;
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_slice_2483_; lean_object* v_nextIt_2485_; 
v___x_2480_ = lean_string_utf8_next_fast(v_fst_2427_, v_searcher_2468_);
v___x_2481_ = lean_nat_sub(v___x_2480_, v_searcher_2468_);
v___x_2482_ = lean_nat_add(v_searcher_2468_, v___x_2481_);
lean_dec(v___x_2481_);
v_slice_2483_ = l_String_Slice_subslice_x21(v___x_2430_, v_currPos_2467_, v_searcher_2468_);
lean_inc(v___x_2482_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2482_);
lean_ctor_set(v___x_2470_, 0, v___x_2482_);
v_nextIt_2485_ = v___x_2470_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2482_);
v_nextIt_2485_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v_startInclusive_2486_; lean_object* v_endExclusive_2487_; 
v_startInclusive_2486_ = lean_ctor_get(v_slice_2483_, 0);
lean_inc(v_startInclusive_2486_);
v_endExclusive_2487_ = lean_ctor_get(v_slice_2483_, 1);
lean_inc(v_endExclusive_2487_);
lean_dec_ref(v_slice_2483_);
v_it_2453_ = v_nextIt_2485_;
v_startInclusive_2454_ = v_startInclusive_2486_;
v_endExclusive_2455_ = v_endExclusive_2487_;
goto v___jp_2452_;
}
}
}
else
{
lean_object* v___x_2489_; 
lean_del_object(v___x_2470_);
lean_dec(v_searcher_2468_);
v___x_2489_ = lean_box(1);
v_it_2453_ = v___x_2489_;
v_startInclusive_2454_ = v_currPos_2467_;
v_endExclusive_2455_ = v___x_2428_;
goto v___jp_2452_;
}
}
}
else
{
lean_dec_ref(v_recur_2434_);
lean_dec(v___x_2428_);
return v_acc_2432_;
}
v___jp_2435_:
{
if (lean_obj_tag(v_acc_2432_) == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_out_2437_);
v___x_2439_ = lean_apply_4(v_recur_2434_, v_it_2436_, v___x_2438_, lean_box(0), lean_box(0));
return v___x_2439_;
}
else
{
lean_object* v_val_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2451_; 
v_val_2440_ = lean_ctor_get(v_acc_2432_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_acc_2432_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2442_ = v_acc_2432_;
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_val_2440_);
lean_dec(v_acc_2432_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2444_ = lean_string_utf8_extract_fast(v___x_2424_, v___x_2425_, v___x_2426_);
v___x_2445_ = lean_string_append(v_val_2440_, v___x_2444_);
lean_dec_ref(v___x_2444_);
v___x_2446_ = lean_string_append(v___x_2445_, v_out_2437_);
lean_dec_ref(v_out_2437_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2446_);
v___x_2448_ = v___x_2442_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_apply_4(v_recur_2434_, v_it_2436_, v___x_2448_, lean_box(0), lean_box(0));
return v___x_2449_;
}
}
}
}
v___jp_2452_:
{
lean_object* v___x_2456_; uint32_t v___x_2457_; uint32_t v___x_2458_; uint8_t v___x_2459_; 
v___x_2456_ = lean_string_utf8_extract_fast(v_fst_2427_, v_startInclusive_2454_, v_endExclusive_2455_);
lean_dec(v_endExclusive_2455_);
lean_dec(v_startInclusive_2454_);
v___x_2457_ = lean_string_utf8_get(v___x_2456_, v___x_2425_);
v___x_2458_ = 97;
v___x_2459_ = lean_uint32_dec_le(v___x_2458_, v___x_2457_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_string_utf8_set(v___x_2456_, v___x_2425_, v___x_2457_);
v_it_2436_ = v_it_2453_;
v_out_2437_ = v___x_2460_;
goto v___jp_2435_;
}
else
{
uint32_t v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = 122;
v___x_2462_ = lean_uint32_dec_le(v___x_2457_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_string_utf8_set(v___x_2456_, v___x_2425_, v___x_2457_);
v_it_2436_ = v_it_2453_;
v_out_2437_ = v___x_2463_;
goto v___jp_2435_;
}
else
{
uint32_t v___x_2464_; uint32_t v___x_2465_; lean_object* v___x_2466_; 
v___x_2464_ = 4294967264;
v___x_2465_ = lean_uint32_add(v___x_2457_, v___x_2464_);
v___x_2466_ = lean_string_utf8_set(v___x_2456_, v___x_2425_, v___x_2465_);
v_it_2436_ = v_it_2453_;
v_out_2437_ = v___x_2466_;
goto v___jp_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__0___boxed(lean_object* v___x_2491_, lean_object* v___x_2492_, lean_object* v___x_2493_, lean_object* v_fst_2494_, lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v___x_2497_, lean_object* v_it_2498_, lean_object* v_acc_2499_, lean_object* v_hP_2500_, lean_object* v_recur_2501_){
_start:
{
uint32_t v___x_1744__boxed_2502_; lean_object* v_res_2503_; 
v___x_1744__boxed_2502_ = lean_unbox_uint32(v___x_2496_);
lean_dec(v___x_2496_);
v_res_2503_ = l_Std_Http_Headers_instToString___lam__0(v___x_2491_, v___x_2492_, v___x_2493_, v_fst_2494_, v___x_2495_, v___x_1744__boxed_2502_, v___x_2497_, v_it_2498_, v_acc_2499_, v_hP_2500_, v_recur_2501_);
lean_dec_ref(v___x_2497_);
lean_dec_ref(v_fst_2494_);
lean_dec(v___x_2493_);
lean_dec(v___x_2492_);
lean_dec_ref(v___x_2491_);
return v_res_2503_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_2508_ = lean_string_utf8_byte_size(v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = 45;
v___x_2510_ = lean_box_uint32(v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__1(lean_object* v_x_2511_){
_start:
{
lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v___y_2515_; lean_object* v___f_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_it_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v_fst_2512_ = lean_ctor_get(v_x_2511_, 0);
lean_inc_n(v_fst_2512_, 2);
v_snd_2513_ = lean_ctor_get(v_x_2511_, 1);
lean_inc(v_snd_2513_);
lean_dec_ref(v_x_2511_);
v___f_2519_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_string_utf8_byte_size(v_fst_2512_);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v_fst_2512_);
lean_ctor_set(v___x_2522_, 1, v___x_2520_);
lean_ctor_set(v___x_2522_, 2, v___x_2521_);
lean_inc_ref(v___x_2522_);
v_it_2523_ = l_String_Slice_splitToSubslice___redArg(v___x_2522_, v___f_2519_);
v___x_2524_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_2525_ = lean_obj_once(&l_Std_Http_Headers_instToString___lam__1___closed__3, &l_Std_Http_Headers_instToString___lam__1___closed__3_once, _init_l_Std_Http_Headers_instToString___lam__1___closed__3);
v___x_2526_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_2527_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instToString___lam__0___boxed), 11, 7);
lean_closure_set(v___f_2527_, 0, v___x_2524_);
lean_closure_set(v___f_2527_, 1, v___x_2520_);
lean_closure_set(v___f_2527_, 2, v___x_2525_);
lean_closure_set(v___f_2527_, 3, v_fst_2512_);
lean_closure_set(v___f_2527_, 4, v___x_2521_);
lean_closure_set(v___f_2527_, 5, v___x_2526_);
lean_closure_set(v___f_2527_, 6, v___x_2522_);
v___x_2528_ = lean_box(0);
v___x_2529_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2527_, v_it_2523_, v___x_2528_, lean_box(0));
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_2515_ = v___x_2530_;
goto v___jp_2514_;
}
else
{
lean_object* v_val_2531_; 
v_val_2531_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_val_2531_);
lean_dec_ref_known(v___x_2529_, 1);
v___y_2515_ = v_val_2531_;
goto v___jp_2514_;
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_2517_ = lean_string_append(v___y_2515_, v___x_2516_);
v___x_2518_ = lean_string_append(v___x_2517_, v_snd_2513_);
lean_dec(v_snd_2513_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instToString___lam__2(lean_object* v___f_2533_, lean_object* v_headers_2534_){
_start:
{
lean_object* v_entries_2535_; lean_object* v___x_2536_; size_t v_sz_2537_; size_t v___x_2538_; lean_object* v_pairs_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_entries_2535_ = lean_ctor_get(v_headers_2534_, 0);
lean_inc_ref(v_entries_2535_);
lean_dec_ref(v_headers_2534_);
v___x_2536_ = ((lean_object*)(l_Std_Http_Headers_getAll___redArg___closed__9));
v_sz_2537_ = lean_array_size(v_entries_2535_);
v___x_2538_ = ((size_t)0ULL);
v_pairs_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2536_, v___f_2533_, v_sz_2537_, v___x_2538_, v_entries_2535_);
v___x_2540_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_2541_ = lean_array_to_list(v_pairs_2539_);
v___x_2542_ = l_String_intercalate(v___x_2540_, v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0(lean_object* v___x_2547_, lean_object* v___x_2548_, lean_object* v___x_2549_, lean_object* v_name_2550_, lean_object* v___x_2551_, uint32_t v___x_2552_, lean_object* v___x_2553_, lean_object* v_it_2554_, lean_object* v_acc_2555_, lean_object* v_hP_2556_, lean_object* v_recur_2557_){
_start:
{
lean_object* v_it_2559_; lean_object* v_out_2560_; lean_object* v_it_2576_; lean_object* v_startInclusive_2577_; lean_object* v_endExclusive_2578_; 
if (lean_obj_tag(v_it_2554_) == 0)
{
lean_object* v_currPos_2590_; lean_object* v_searcher_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2613_; 
v_currPos_2590_ = lean_ctor_get(v_it_2554_, 0);
v_searcher_2591_ = lean_ctor_get(v_it_2554_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_it_2554_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2593_ = v_it_2554_;
v_isShared_2594_ = v_isSharedCheck_2613_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_searcher_2591_);
lean_inc(v_currPos_2590_);
lean_dec(v_it_2554_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2613_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_nat_dec_eq(v_searcher_2591_, v___x_2551_);
if (v___x_2595_ == 0)
{
uint32_t v___x_2596_; uint8_t v___x_2597_; 
lean_dec(v___x_2551_);
v___x_2596_ = lean_string_utf8_get_fast(v_name_2550_, v_searcher_2591_);
v___x_2597_ = lean_uint32_dec_eq(v___x_2596_, v___x_2552_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
v___x_2598_ = lean_string_utf8_next_fast(v_name_2550_, v_searcher_2591_);
lean_dec(v_searcher_2591_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2598_);
v___x_2600_ = v___x_2593_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_currPos_2590_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_apply_4(v_recur_2557_, v___x_2600_, v_acc_2555_, lean_box(0), lean_box(0));
return v___x_2601_;
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_slice_2606_; lean_object* v_nextIt_2608_; 
v___x_2603_ = lean_string_utf8_next_fast(v_name_2550_, v_searcher_2591_);
v___x_2604_ = lean_nat_sub(v___x_2603_, v_searcher_2591_);
v___x_2605_ = lean_nat_add(v_searcher_2591_, v___x_2604_);
lean_dec(v___x_2604_);
v_slice_2606_ = l_String_Slice_subslice_x21(v___x_2553_, v_currPos_2590_, v_searcher_2591_);
lean_inc(v___x_2605_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v___x_2605_);
lean_ctor_set(v___x_2593_, 0, v___x_2605_);
v_nextIt_2608_ = v___x_2593_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v___x_2605_);
v_nextIt_2608_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v_startInclusive_2609_; lean_object* v_endExclusive_2610_; 
v_startInclusive_2609_ = lean_ctor_get(v_slice_2606_, 0);
lean_inc(v_startInclusive_2609_);
v_endExclusive_2610_ = lean_ctor_get(v_slice_2606_, 1);
lean_inc(v_endExclusive_2610_);
lean_dec_ref(v_slice_2606_);
v_it_2576_ = v_nextIt_2608_;
v_startInclusive_2577_ = v_startInclusive_2609_;
v_endExclusive_2578_ = v_endExclusive_2610_;
goto v___jp_2575_;
}
}
}
else
{
lean_object* v___x_2612_; 
lean_del_object(v___x_2593_);
lean_dec(v_searcher_2591_);
v___x_2612_ = lean_box(1);
v_it_2576_ = v___x_2612_;
v_startInclusive_2577_ = v_currPos_2590_;
v_endExclusive_2578_ = v___x_2551_;
goto v___jp_2575_;
}
}
}
else
{
lean_dec_ref(v_recur_2557_);
lean_dec(v___x_2551_);
return v_acc_2555_;
}
v___jp_2558_:
{
if (lean_obj_tag(v_acc_2555_) == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_out_2560_);
v___x_2562_ = lean_apply_4(v_recur_2557_, v_it_2559_, v___x_2561_, lean_box(0), lean_box(0));
return v___x_2562_;
}
else
{
lean_object* v_val_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2574_; 
v_val_2563_ = lean_ctor_get(v_acc_2555_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_acc_2555_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2565_ = v_acc_2555_;
v_isShared_2566_ = v_isSharedCheck_2574_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_val_2563_);
lean_dec(v_acc_2555_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2574_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2567_ = lean_string_utf8_extract_fast(v___x_2547_, v___x_2548_, v___x_2549_);
v___x_2568_ = lean_string_append(v_val_2563_, v___x_2567_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = lean_string_append(v___x_2568_, v_out_2560_);
lean_dec_ref(v_out_2560_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2569_);
v___x_2571_ = v___x_2565_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_apply_4(v_recur_2557_, v_it_2559_, v___x_2571_, lean_box(0), lean_box(0));
return v___x_2572_;
}
}
}
}
v___jp_2575_:
{
lean_object* v___x_2579_; uint32_t v___x_2580_; uint32_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2579_ = lean_string_utf8_extract_fast(v_name_2550_, v_startInclusive_2577_, v_endExclusive_2578_);
lean_dec(v_endExclusive_2578_);
lean_dec(v_startInclusive_2577_);
v___x_2580_ = lean_string_utf8_get(v___x_2579_, v___x_2548_);
v___x_2581_ = 97;
v___x_2582_ = lean_uint32_dec_le(v___x_2581_, v___x_2580_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_string_utf8_set(v___x_2579_, v___x_2548_, v___x_2580_);
v_it_2559_ = v_it_2576_;
v_out_2560_ = v___x_2583_;
goto v___jp_2558_;
}
else
{
uint32_t v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = 122;
v___x_2585_ = lean_uint32_dec_le(v___x_2580_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_string_utf8_set(v___x_2579_, v___x_2548_, v___x_2580_);
v_it_2559_ = v_it_2576_;
v_out_2560_ = v___x_2586_;
goto v___jp_2558_;
}
else
{
uint32_t v___x_2587_; uint32_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = 4294967264;
v___x_2588_ = lean_uint32_add(v___x_2580_, v___x_2587_);
v___x_2589_ = lean_string_utf8_set(v___x_2579_, v___x_2548_, v___x_2588_);
v_it_2559_ = v_it_2576_;
v_out_2560_ = v___x_2589_;
goto v___jp_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__0___boxed(lean_object* v___x_2614_, lean_object* v___x_2615_, lean_object* v___x_2616_, lean_object* v_name_2617_, lean_object* v___x_2618_, lean_object* v___x_2619_, lean_object* v___x_2620_, lean_object* v_it_2621_, lean_object* v_acc_2622_, lean_object* v_hP_2623_, lean_object* v_recur_2624_){
_start:
{
uint32_t v___x_916__boxed_2625_; lean_object* v_res_2626_; 
v___x_916__boxed_2625_ = lean_unbox_uint32(v___x_2619_);
lean_dec(v___x_2619_);
v_res_2626_ = l_Std_Http_Headers_instEncodeV11___lam__0(v___x_2614_, v___x_2615_, v___x_2616_, v_name_2617_, v___x_2618_, v___x_916__boxed_2625_, v___x_2620_, v_it_2621_, v_acc_2622_, v_hP_2623_, v_recur_2624_);
lean_dec_ref(v___x_2620_);
lean_dec_ref(v_name_2617_);
lean_dec(v___x_2616_);
lean_dec(v___x_2615_);
lean_dec_ref(v___x_2614_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1(lean_object* v_buf_2627_, lean_object* v_name_2628_, lean_object* v_value_2629_){
_start:
{
lean_object* v___y_2631_; lean_object* v___f_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v_it_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___f_2650_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__1));
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_string_utf8_byte_size(v_name_2628_);
lean_inc_ref(v_name_2628_);
v___x_2653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2653_, 0, v_name_2628_);
lean_ctor_set(v___x_2653_, 1, v___x_2651_);
lean_ctor_set(v___x_2653_, 2, v___x_2652_);
lean_inc_ref(v___x_2653_);
v_it_2654_ = l_String_Slice_splitToSubslice___redArg(v___x_2653_, v___f_2650_);
v___x_2655_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__2));
v___x_2656_ = lean_obj_once(&l_Std_Http_Headers_instToString___lam__1___closed__3, &l_Std_Http_Headers_instToString___lam__1___closed__3_once, _init_l_Std_Http_Headers_instToString___lam__1___closed__3);
v___x_2657_ = l_Std_Http_Headers_instToString___lam__1___boxed__const__1;
v___f_2658_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_2658_, 0, v___x_2655_);
lean_closure_set(v___f_2658_, 1, v___x_2651_);
lean_closure_set(v___f_2658_, 2, v___x_2656_);
lean_closure_set(v___f_2658_, 3, v_name_2628_);
lean_closure_set(v___f_2658_, 4, v___x_2652_);
lean_closure_set(v___f_2658_, 5, v___x_2657_);
lean_closure_set(v___f_2658_, 6, v___x_2653_);
v___x_2659_ = lean_box(0);
v___x_2660_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2658_, v_it_2654_, v___x_2659_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2661_; 
v___x_2661_ = ((lean_object*)(l_Std_Http_Headers_get_x21___closed__0));
v___y_2631_ = v___x_2661_;
goto v___jp_2630_;
}
else
{
lean_object* v_val_2662_; 
v_val_2662_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___x_2660_, 1);
v___y_2631_ = v_val_2662_;
goto v___jp_2630_;
}
v___jp_2630_:
{
lean_object* v_data_2632_; lean_object* v_size_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2649_; 
v_data_2632_ = lean_ctor_get(v_buf_2627_, 0);
v_size_2633_ = lean_ctor_get(v_buf_2627_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_buf_2627_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2635_ = v_buf_2627_;
v_isShared_2636_ = v_isSharedCheck_2649_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_size_2633_);
lean_inc(v_data_2632_);
lean_dec(v_buf_2627_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2649_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2637_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__1___closed__0));
v___x_2638_ = lean_string_append(v___y_2631_, v___x_2637_);
v___x_2639_ = lean_string_append(v___x_2638_, v_value_2629_);
v___x_2640_ = ((lean_object*)(l_Std_Http_Headers_instToString___lam__2___closed__0));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
v___x_2642_ = lean_string_to_utf8(v___x_2641_);
lean_dec_ref(v___x_2641_);
lean_inc_ref(v___x_2642_);
v___x_2643_ = lean_array_push(v_data_2632_, v___x_2642_);
v___x_2644_ = lean_byte_array_size(v___x_2642_);
lean_dec_ref(v___x_2642_);
v___x_2645_ = lean_nat_add(v_size_2633_, v___x_2644_);
lean_dec(v_size_2633_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2645_);
lean_ctor_set(v___x_2635_, 0, v___x_2643_);
v___x_2647_ = v___x_2635_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__1___boxed(lean_object* v_buf_2663_, lean_object* v_name_2664_, lean_object* v_value_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Std_Http_Headers_instEncodeV11___lam__1(v_buf_2663_, v_name_2664_, v_value_2665_);
lean_dec_ref(v_value_2665_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2(lean_object* v___f_2667_, lean_object* v_buffer_2668_, lean_object* v_headers_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Std_Http_Headers_fold___redArg(v_headers_2669_, v_buffer_2668_, v___f_2667_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instEncodeV11___lam__2___boxed(lean_object* v___f_2671_, lean_object* v_buffer_2672_, lean_object* v_headers_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Std_Http_Headers_instEncodeV11___lam__2(v___f_2671_, v_buffer_2672_, v_headers_2673_);
lean_dec_ref(v_headers_2673_);
return v_res_2674_;
}
}
static lean_object* _init_l_Std_Http_Headers_instEmptyCollection(void){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
return v___x_2679_;
}
}
static lean_object* _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = lean_nat_add(v___x_2681_, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_unsigned_to_nat(4u);
v___x_2684_ = lean_obj_once(&l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0, &l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0_once, _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0);
v___x_2685_ = lean_nat_mul(v___x_2684_, v___x_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instSingletonProdNameValue___lam__1(lean_object* v_x_2686_){
_start:
{
lean_object* v_fst_2687_; lean_object* v___x_2688_; lean_object* v_entries_2689_; lean_object* v_indexes_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v_i_2693_; lean_object* v_entries_2694_; lean_object* v___x_2695_; 
v_fst_2687_ = lean_ctor_get(v_x_2686_, 0);
lean_inc_n(v_fst_2687_, 2);
v___x_2688_ = lean_obj_once(&l_Std_Http_Headers_empty___closed__0, &l_Std_Http_Headers_empty___closed__0_once, _init_l_Std_Http_Headers_empty___closed__0);
v_entries_2689_ = lean_ctor_get(v___x_2688_, 0);
v_indexes_2690_ = lean_ctor_get(v___x_2688_, 1);
v___f_2691_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_2692_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_2693_ = lean_array_get_size(v_entries_2689_);
lean_inc_ref(v_entries_2689_);
v_entries_2694_ = lean_array_push(v_entries_2689_, v_x_2686_);
v___x_2695_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2691_, v___f_2692_, v_indexes_2690_, v_fst_2687_);
switch(lean_obj_tag(v___x_2695_))
{
case 0:
{
lean_object* v_index_2696_; lean_object* v_value_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v_val_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v_index_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_index_2696_);
v_value_2697_ = lean_ctor_get(v___x_2695_, 2);
lean_inc(v_value_2697_);
lean_dec_ref_known(v___x_2695_, 3);
v___x_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_value_2697_);
v___x_2699_ = l_Std_Http_Headers_insert___lam__0(v_i_2693_, v___x_2698_);
v_val_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_val_2700_);
lean_dec(v___x_2699_);
v___x_2701_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_indexes_2690_);
v___x_2702_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2690_, v___x_2701_, v_index_2696_, v_fst_2687_, v_val_2700_);
lean_dec(v_index_2696_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_entries_2694_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
return v___x_2703_;
}
case 1:
{
lean_object* v_index_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_val_2707_; lean_object* v___y_2709_; lean_object* v_i_2710_; lean_object* v_keyArray_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_index_2704_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_index_2704_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2705_ = lean_box(0);
v___x_2706_ = l_Std_Http_Headers_insert___lam__0(v_i_2693_, v___x_2705_);
v_val_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_val_2707_);
lean_dec(v___x_2706_);
v_keyArray_2728_ = lean_ctor_get(v_indexes_2690_, 1);
v___x_2729_ = lean_obj_once(&l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0, &l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0_once, _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0);
v___x_2730_ = lean_array_get_size(v_keyArray_2728_);
v___x_2731_ = lean_nat_dec_lt(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
lean_dec(v_index_2704_);
goto v___jp_2716_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2732_ = lean_obj_once(&l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1, &l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1_once, _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1);
v___x_2733_ = lean_unsigned_to_nat(3u);
v___x_2734_ = lean_nat_mul(v___x_2730_, v___x_2733_);
v___x_2735_ = lean_nat_dec_le(v___x_2732_, v___x_2734_);
lean_dec(v___x_2734_);
if (v___x_2735_ == 0)
{
lean_dec(v_index_2704_);
goto v___jp_2716_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_inc_ref(v_indexes_2690_);
v___x_2736_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2690_, v___x_2729_, v_index_2704_, v_fst_2687_, v_val_2707_);
lean_dec(v_index_2704_);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v_entries_2694_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
return v___x_2737_;
}
}
v___jp_2708_:
{
lean_object* v_size_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_size_2711_ = lean_ctor_get(v___y_2709_, 0);
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = lean_nat_add(v_size_2711_, v___x_2712_);
v___x_2714_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2709_, v___x_2713_, v_i_2710_, v_fst_2687_, v_val_2707_);
lean_dec(v_i_2710_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_entries_2694_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
return v___x_2715_;
}
v___jp_2716_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_inc_ref(v_indexes_2690_);
v___x_2717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2691_, v___f_2692_, v_indexes_2690_);
lean_inc(v_fst_2687_);
v___x_2718_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2691_, v___f_2692_, v___x_2717_, v_fst_2687_);
switch(lean_obj_tag(v___x_2718_))
{
case 0:
{
lean_object* v_index_2719_; lean_object* v_size_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_index_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_index_2719_);
lean_dec_ref_known(v___x_2718_, 3);
v_size_2720_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_size_2720_);
v___x_2721_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2717_, v_size_2720_, v_index_2719_, v_fst_2687_, v_val_2707_);
lean_dec(v_index_2719_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_entries_2694_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
return v___x_2722_;
}
case 1:
{
lean_object* v_index_2723_; 
v_index_2723_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_index_2723_);
lean_dec_ref_known(v___x_2718_, 1);
v___y_2709_ = v___x_2717_;
v_i_2710_ = v_index_2723_;
goto v___jp_2708_;
}
default: 
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2717_, v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_index_2726_; 
v_index_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_index_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___y_2709_ = v___x_2717_;
v_i_2710_ = v_index_2726_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2727_; 
lean_dec(v_val_2707_);
lean_dec(v_fst_2687_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_entries_2694_);
lean_ctor_set(v___x_2727_, 1, v___x_2717_);
return v___x_2727_;
}
}
}
}
}
default: 
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v_val_2740_; lean_object* v___y_2742_; lean_object* v_i_2743_; lean_object* v___y_2750_; lean_object* v_keyArray_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2738_ = lean_box(0);
v___x_2739_ = l_Std_Http_Headers_insert___lam__0(v_i_2693_, v___x_2738_);
v_val_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_val_2740_);
lean_dec(v___x_2739_);
v_keyArray_2761_ = lean_ctor_get(v_indexes_2690_, 1);
v___x_2762_ = lean_obj_once(&l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0, &l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0_once, _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__0);
v___x_2763_ = lean_array_get_size(v_keyArray_2761_);
v___x_2764_ = lean_nat_dec_lt(v___x_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
lean_inc_ref(v_indexes_2690_);
v___x_2765_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2691_, v___f_2692_, v_indexes_2690_);
v___y_2750_ = v___x_2765_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2766_ = lean_obj_once(&l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1, &l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1_once, _init_l_Std_Http_Headers_instSingletonProdNameValue___lam__1___closed__1);
v___x_2767_ = lean_unsigned_to_nat(3u);
v___x_2768_ = lean_nat_mul(v___x_2763_, v___x_2767_);
v___x_2769_ = lean_nat_dec_le(v___x_2766_, v___x_2768_);
lean_dec(v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_inc_ref(v_indexes_2690_);
v___x_2770_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2691_, v___f_2692_, v_indexes_2690_);
v___y_2750_ = v___x_2770_;
goto v___jp_2749_;
}
else
{
lean_inc_ref(v_indexes_2690_);
v___y_2750_ = v_indexes_2690_;
goto v___jp_2749_;
}
}
v___jp_2741_:
{
lean_object* v_size_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_size_2744_ = lean_ctor_get(v___y_2742_, 0);
v___x_2745_ = lean_unsigned_to_nat(1u);
v___x_2746_ = lean_nat_add(v_size_2744_, v___x_2745_);
v___x_2747_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2742_, v___x_2746_, v_i_2743_, v_fst_2687_, v_val_2740_);
lean_dec(v_i_2743_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v_entries_2694_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
return v___x_2748_;
}
v___jp_2749_:
{
lean_object* v___x_2751_; 
lean_inc(v_fst_2687_);
v___x_2751_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2691_, v___f_2692_, v___y_2750_, v_fst_2687_);
switch(lean_obj_tag(v___x_2751_))
{
case 0:
{
lean_object* v_index_2752_; lean_object* v_size_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_index_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_index_2752_);
lean_dec_ref_known(v___x_2751_, 3);
v_size_2753_ = lean_ctor_get(v___y_2750_, 0);
lean_inc(v_size_2753_);
v___x_2754_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2750_, v_size_2753_, v_index_2752_, v_fst_2687_, v_val_2740_);
lean_dec(v_index_2752_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_entries_2694_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
return v___x_2755_;
}
case 1:
{
lean_object* v_index_2756_; 
v_index_2756_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_index_2756_);
lean_dec_ref_known(v___x_2751_, 1);
v___y_2742_ = v___y_2750_;
v_i_2743_ = v_index_2756_;
goto v___jp_2741_;
}
default: 
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_unsigned_to_nat(0u);
v___x_2758_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2750_, v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_index_2759_; 
v_index_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_index_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v___y_2742_ = v___y_2750_;
v_i_2743_ = v_index_2759_;
goto v___jp_2741_;
}
else
{
lean_object* v___x_2760_; 
lean_dec(v_val_2740_);
lean_dec(v_fst_2687_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v_entries_2694_);
lean_ctor_set(v___x_2760_, 1, v___y_2750_);
return v___x_2760_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instInsertProdNameValue___lam__1(lean_object* v_x_2773_, lean_object* v_s_2774_){
_start:
{
lean_object* v_fst_2775_; lean_object* v_entries_2776_; lean_object* v_indexes_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2873_; 
v_fst_2775_ = lean_ctor_get(v_x_2773_, 0);
lean_inc(v_fst_2775_);
v_entries_2776_ = lean_ctor_get(v_s_2774_, 0);
v_indexes_2777_ = lean_ctor_get(v_s_2774_, 1);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_s_2774_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2779_ = v_s_2774_;
v_isShared_2780_ = v_isSharedCheck_2873_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_indexes_2777_);
lean_inc(v_entries_2776_);
lean_dec(v_s_2774_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2873_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___f_2781_; lean_object* v___f_2782_; lean_object* v_i_2783_; lean_object* v_entries_2784_; lean_object* v___x_2785_; 
v___f_2781_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__0));
v___f_2782_ = ((lean_object*)(l_Std_Http_instDecidableMemNameHeaders___closed__1));
v_i_2783_ = lean_array_get_size(v_entries_2776_);
v_entries_2784_ = lean_array_push(v_entries_2776_, v_x_2773_);
lean_inc(v_fst_2775_);
v___x_2785_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2781_, v___f_2782_, v_indexes_2777_, v_fst_2775_);
switch(lean_obj_tag(v___x_2785_))
{
case 0:
{
lean_object* v_index_2786_; lean_object* v_value_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_val_2790_; lean_object* v_size_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v_index_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_index_2786_);
v_value_2787_ = lean_ctor_get(v___x_2785_, 2);
lean_inc(v_value_2787_);
lean_dec_ref_known(v___x_2785_, 3);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_value_2787_);
v___x_2789_ = l_Std_Http_Headers_insert___lam__0(v_i_2783_, v___x_2788_);
v_val_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_val_2790_);
lean_dec(v___x_2789_);
v_size_2791_ = lean_ctor_get(v_indexes_2777_, 0);
lean_inc(v_size_2791_);
v___x_2792_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2777_, v_size_2791_, v_index_2786_, v_fst_2775_, v_val_2790_);
lean_dec(v_index_2786_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v___x_2792_);
lean_ctor_set(v___x_2779_, 0, v_entries_2784_);
v___x_2794_ = v___x_2779_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_entries_2784_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
case 1:
{
lean_object* v_index_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_val_2799_; lean_object* v___y_2801_; lean_object* v_i_2802_; lean_object* v_size_2822_; lean_object* v_keyArray_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_index_2796_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_index_2796_);
lean_dec_ref_known(v___x_2785_, 1);
v___x_2797_ = lean_box(0);
v___x_2798_ = l_Std_Http_Headers_insert___lam__0(v_i_2783_, v___x_2797_);
v_val_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_val_2799_);
lean_dec(v___x_2798_);
v_size_2822_ = lean_ctor_get(v_indexes_2777_, 0);
v_keyArray_2823_ = lean_ctor_get(v_indexes_2777_, 1);
v___x_2824_ = lean_unsigned_to_nat(1u);
v___x_2825_ = lean_nat_add(v_size_2822_, v___x_2824_);
v___x_2826_ = lean_array_get_size(v_keyArray_2823_);
v___x_2827_ = lean_nat_dec_lt(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec(v___x_2825_);
lean_dec(v_index_2796_);
goto v___jp_2810_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2828_ = lean_unsigned_to_nat(4u);
v___x_2829_ = lean_nat_mul(v___x_2825_, v___x_2828_);
v___x_2830_ = lean_unsigned_to_nat(3u);
v___x_2831_ = lean_nat_mul(v___x_2826_, v___x_2830_);
v___x_2832_ = lean_nat_dec_le(v___x_2829_, v___x_2831_);
lean_dec(v___x_2831_);
lean_dec(v___x_2829_);
if (v___x_2832_ == 0)
{
lean_dec(v___x_2825_);
lean_dec(v_index_2796_);
goto v___jp_2810_;
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_del_object(v___x_2779_);
v___x_2833_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2777_, v___x_2825_, v_index_2796_, v_fst_2775_, v_val_2799_);
lean_dec(v_index_2796_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_entries_2784_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
return v___x_2834_;
}
}
v___jp_2800_:
{
lean_object* v_size_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v_size_2803_ = lean_ctor_get(v___y_2801_, 0);
v___x_2804_ = lean_unsigned_to_nat(1u);
v___x_2805_ = lean_nat_add(v_size_2803_, v___x_2804_);
v___x_2806_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2801_, v___x_2805_, v_i_2802_, v_fst_2775_, v_val_2799_);
lean_dec(v_i_2802_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v___x_2806_);
lean_ctor_set(v___x_2779_, 0, v_entries_2784_);
v___x_2808_ = v___x_2779_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_entries_2784_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
v___jp_2810_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2781_, v___f_2782_, v_indexes_2777_);
lean_inc(v_fst_2775_);
v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2781_, v___f_2782_, v___x_2811_, v_fst_2775_);
switch(lean_obj_tag(v___x_2812_))
{
case 0:
{
lean_object* v_index_2813_; lean_object* v_size_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_del_object(v___x_2779_);
v_index_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_index_2813_);
lean_dec_ref_known(v___x_2812_, 3);
v_size_2814_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_size_2814_);
v___x_2815_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2811_, v_size_2814_, v_index_2813_, v_fst_2775_, v_val_2799_);
lean_dec(v_index_2813_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v_entries_2784_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
return v___x_2816_;
}
case 1:
{
lean_object* v_index_2817_; 
v_index_2817_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_index_2817_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2801_ = v___x_2811_;
v_i_2802_ = v_index_2817_;
goto v___jp_2800_;
}
default: 
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2811_, v___x_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_index_2820_; 
v_index_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_index_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___y_2801_ = v___x_2811_;
v_i_2802_ = v_index_2820_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2821_; 
lean_dec(v_val_2799_);
lean_del_object(v___x_2779_);
lean_dec(v_fst_2775_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_entries_2784_);
lean_ctor_set(v___x_2821_, 1, v___x_2811_);
return v___x_2821_;
}
}
}
}
}
default: 
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_val_2837_; lean_object* v___y_2839_; lean_object* v_i_2840_; lean_object* v___y_2849_; lean_object* v_size_2860_; lean_object* v_keyArray_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2835_ = lean_box(0);
v___x_2836_ = l_Std_Http_Headers_insert___lam__0(v_i_2783_, v___x_2835_);
v_val_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_val_2837_);
lean_dec(v___x_2836_);
v_size_2860_ = lean_ctor_get(v_indexes_2777_, 0);
v_keyArray_2861_ = lean_ctor_get(v_indexes_2777_, 1);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_add(v_size_2860_, v___x_2862_);
v___x_2864_ = lean_array_get_size(v_keyArray_2861_);
v___x_2865_ = lean_nat_dec_lt(v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v___x_2863_);
v___x_2866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2781_, v___f_2782_, v_indexes_2777_);
v___y_2849_ = v___x_2866_;
goto v___jp_2848_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2867_ = lean_unsigned_to_nat(4u);
v___x_2868_ = lean_nat_mul(v___x_2863_, v___x_2867_);
lean_dec(v___x_2863_);
v___x_2869_ = lean_unsigned_to_nat(3u);
v___x_2870_ = lean_nat_mul(v___x_2864_, v___x_2869_);
v___x_2871_ = lean_nat_dec_le(v___x_2868_, v___x_2870_);
lean_dec(v___x_2870_);
lean_dec(v___x_2868_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2781_, v___f_2782_, v_indexes_2777_);
v___y_2849_ = v___x_2872_;
goto v___jp_2848_;
}
else
{
v___y_2849_ = v_indexes_2777_;
goto v___jp_2848_;
}
}
v___jp_2838_:
{
lean_object* v_size_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v_size_2841_ = lean_ctor_get(v___y_2839_, 0);
v___x_2842_ = lean_unsigned_to_nat(1u);
v___x_2843_ = lean_nat_add(v_size_2841_, v___x_2842_);
v___x_2844_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2839_, v___x_2843_, v_i_2840_, v_fst_2775_, v_val_2837_);
lean_dec(v_i_2840_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 1, v___x_2844_);
lean_ctor_set(v___x_2779_, 0, v_entries_2784_);
v___x_2846_ = v___x_2779_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_entries_2784_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
v___jp_2848_:
{
lean_object* v___x_2850_; 
lean_inc(v_fst_2775_);
v___x_2850_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2781_, v___f_2782_, v___y_2849_, v_fst_2775_);
switch(lean_obj_tag(v___x_2850_))
{
case 0:
{
lean_object* v_index_2851_; lean_object* v_size_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_del_object(v___x_2779_);
v_index_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_index_2851_);
lean_dec_ref_known(v___x_2850_, 3);
v_size_2852_ = lean_ctor_get(v___y_2849_, 0);
lean_inc(v_size_2852_);
v___x_2853_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2849_, v_size_2852_, v_index_2851_, v_fst_2775_, v_val_2837_);
lean_dec(v_index_2851_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_entries_2784_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
return v___x_2854_;
}
case 1:
{
lean_object* v_index_2855_; 
v_index_2855_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_index_2855_);
lean_dec_ref_known(v___x_2850_, 1);
v___y_2839_ = v___y_2849_;
v_i_2840_ = v_index_2855_;
goto v___jp_2838_;
}
default: 
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2849_, v___x_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_index_2858_; 
v_index_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_index_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___y_2839_ = v___y_2849_;
v_i_2840_ = v_index_2858_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2859_; 
lean_dec(v_val_2837_);
lean_del_object(v___x_2779_);
lean_dec(v_fst_2775_);
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_entries_2784_);
lean_ctor_set(v___x_2859_, 1, v___y_2849_);
return v___x_2859_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0(lean_object* v_f_2878_, lean_object* v_a_2879_, lean_object* v_x_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_apply_2(v_f_2878_, v_a_2879_, v___y_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1(lean_object* v_inst_2883_, lean_object* v_00_u03b2_2884_, lean_object* v_headers_2885_, lean_object* v_b_2886_, lean_object* v_f_2887_){
_start:
{
lean_object* v_entries_2888_; lean_object* v___f_2889_; size_t v_sz_2890_; size_t v___x_2891_; lean_object* v___x_2892_; 
v_entries_2888_ = lean_ctor_get(v_headers_2885_, 0);
lean_inc_ref(v_entries_2888_);
lean_dec_ref(v_headers_2885_);
v___f_2889_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2889_, 0, v_f_2887_);
v_sz_2890_ = lean_array_size(v_entries_2888_);
v___x_2891_ = ((size_t)0ULL);
v___x_2892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2883_, v_entries_2888_, v___f_2889_, v_sz_2890_, v___x_2891_, v_b_2886_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg(lean_object* v_inst_2893_){
_start:
{
lean_object* v___f_2894_; 
v___f_2894_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2894_, 0, v_inst_2893_);
return v___f_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Headers_instForInProdNameValueOfMonad(lean_object* v_m_2895_, lean_object* v_inst_2896_){
_start:
{
lean_object* v___f_2897_; 
v___f_2897_ = lean_alloc_closure((void*)(l_Std_Http_Headers_instForInProdNameValueOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2897_, 0, v_inst_2896_);
return v___f_2897_;
}
}
lean_object* runtime_initialize_Std_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedHeaders_default = _init_l_Std_Http_instInhabitedHeaders_default();
lean_mark_persistent(l_Std_Http_instInhabitedHeaders_default);
l_Std_Http_instInhabitedHeaders = _init_l_Std_Http_instInhabitedHeaders();
lean_mark_persistent(l_Std_Http_instInhabitedHeaders);
l_Std_Http_instMembershipNameHeaders = _init_l_Std_Http_instMembershipNameHeaders();
lean_mark_persistent(l_Std_Http_instMembershipNameHeaders);
l_Std_Http_Headers_empty = _init_l_Std_Http_Headers_empty();
lean_mark_persistent(l_Std_Http_Headers_empty);
l_Std_Http_Headers_instToString___lam__1___boxed__const__1 = _init_l_Std_Http_Headers_instToString___lam__1___boxed__const__1();
lean_mark_persistent(l_Std_Http_Headers_instToString___lam__1___boxed__const__1);
l_Std_Http_Headers_instEmptyCollection = _init_l_Std_Http_Headers_instEmptyCollection();
lean_mark_persistent(l_Std_Http_Headers_instEmptyCollection);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_Headers_Basic(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Headers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Headers(builtin);
}
#ifdef __cplusplus
}
#endif
