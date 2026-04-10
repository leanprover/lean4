// Lean compiler output
// Module: Std.Internal.Http.Data.Chunk
// Imports: public import Std.Internal.Http.Internal public import Std.Internal.Http.Data.Headers public meta import Std.Internal.Http.Internal.String
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Http_Headers_toArray(lean_object*);
lean_object* lean_string_data(lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_toList(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Std_Http_Headers_merge(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_Internal_isToken(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_Http_instInhabitedHeaders_default;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object*);
lean_object* l_UInt32_toUInt8___boxed(lean_object*);
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3_value;
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_0),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_1),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value_aux_2),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4_value;
static const lean_array_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6_value;
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_0),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_1),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value_aux_2),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8_value;
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10_value;
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_0),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_1),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value_aux_2),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11_value;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14_value;
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_0),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_1),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value_aux_2),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15_value;
static const lean_ctor_object l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9_value),((lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5_value)}};
static const lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16_value;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25;
static lean_once_cell_t l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Chunk_instReprExtensionName_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "isValidExtensionName"};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15;
static lean_once_cell_t l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionName_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instReprExtensionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instReprExtensionName_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instReprExtensionName___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instReprExtensionName = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionName_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionName_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionName___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instBEqExtensionName_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instBEqExtensionName_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instBEqExtensionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instBEqExtensionName_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instBEqExtensionName___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instBEqExtensionName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instBEqExtensionName = (const lean_object*)&l_Std_Http_Chunk_instBEqExtensionName___closed__0_value;
static const lean_closure_object l_Std_Http_Chunk_instHashableExtensionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instHashableExtensionName___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instHashableExtensionName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instHashableExtensionName = (const lean_object*)&l_Std_Http_Chunk_instHashableExtensionName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instInhabitedExtensionName = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instToStringExtensionName___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instToStringExtensionName___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instToStringExtensionName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instToStringExtensionName___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instToStringExtensionName___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instToStringExtensionName___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instToStringExtensionName = (const lean_object*)&l_Std_Http_Chunk_instToStringExtensionName___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Chunk_ExtensionName_ofString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Internal.Http.Data.Chunk"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Http.Chunk.ExtensionName.ofString!"};
static const lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid extension name: "};
static const lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2 = (const lean_object*)&l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam;
static const lean_string_object l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "isValidExtensionValue"};
static const lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instReprExtensionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instReprExtensionValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instReprExtensionValue___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instReprExtensionValue = (const lean_object*)&l_Std_Http_Chunk_instReprExtensionValue___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instBEqExtensionValue_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instBEqExtensionValue_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instBEqExtensionValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instBEqExtensionValue_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instBEqExtensionValue___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instBEqExtensionValue___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instBEqExtensionValue = (const lean_object*)&l_Std_Http_Chunk_instBEqExtensionValue___closed__0_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0 = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_ExtensionValue_instInhabited = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_instToString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Chunk_ExtensionValue_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_ExtensionValue_instToString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_ExtensionValue_instToString___closed__0 = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_ExtensionValue_instToString = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_quote(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Chunk_ExtensionValue_ofString_x3f___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Chunk_ExtensionValue_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_ExtensionValue_ofString_x3f___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f___closed__0 = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_ofString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Std.Http.Chunk.ExtensionValue.ofString!"};
static const lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0 = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0_value;
static const lean_string_object l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "invalid extension value: "};
static const lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1 = (const lean_object*)&l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x21(lean_object*);
static const lean_array_object l_Std_Http_instInhabitedChunk_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_instInhabitedChunk_default___closed__0 = (const lean_object*)&l_Std_Http_instInhabitedChunk_default___closed__0_value;
static lean_once_cell_t l_Std_Http_instInhabitedChunk_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instInhabitedChunk_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedChunk_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedChunk;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_empty;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_insertExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_toString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6_value;
static const lean_ctor_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__0_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__1_value)}};
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7_value;
static const lean_ctor_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__7_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__2_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__3_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__4_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__5_value)}};
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8_value;
static const lean_ctor_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__8_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__6_value)}};
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9_value;
static const lean_string_object l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10_value;
static lean_once_cell_t l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11;
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_toUInt8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__0_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instEncodeV11___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___closed__1 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__1_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instEncodeV11___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___closed__2 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__2_value;
static const lean_closure_object l_Std_Http_Chunk_instEncodeV11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Chunk_instEncodeV11___lam__2, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__0_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__1_value),((lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__2_value)} };
static const lean_object* l_Std_Http_Chunk_instEncodeV11___closed__3 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__3_value;
LEAN_EXPORT const lean_object* l_Std_Http_Chunk_instEncodeV11 = (const lean_object*)&l_Std_Http_Chunk_instEncodeV11___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedTrailer_default;
LEAN_EXPORT lean_object* l_Std_Http_instInhabitedTrailer;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_empty;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Trailer_insert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Trailer_insert___closed__0 = (const lean_object*)&l_Std_Http_Trailer_insert___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Trailer_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Trailer_erase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Trailer_erase___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Http_Trailer_insert___closed__0_value),((lean_object*)&l_Std_Http_Chunk_instHashableExtensionName___closed__0_value)} };
static const lean_object* l_Std_Http_Trailer_erase___closed__0 = (const lean_object*)&l_Std_Http_Trailer_erase___closed__0_value;
static lean_once_cell_t l_Std_Http_Trailer_erase___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Trailer_erase___closed__1;
static const lean_array_object l_Std_Http_Trailer_erase___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Trailer_erase___closed__2 = (const lean_object*)&l_Std_Http_Trailer_erase___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Trailer_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0_value;
static const lean_closure_object l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2_value;
static lean_once_cell_t l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "0\r\n"};
static const lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0_value;
static lean_once_cell_t l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1;
static lean_once_cell_t l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2;
static lean_once_cell_t l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Trailer_instEncodeV11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Trailer_instEncodeV11___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Trailer_instEncodeV11___closed__0 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___closed__0_value;
static const lean_closure_object l_Std_Http_Trailer_instEncodeV11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Trailer_instEncodeV11___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Trailer_instEncodeV11___closed__0_value)} };
static const lean_object* l_Std_Http_Trailer_instEncodeV11___closed__1 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Trailer_instEncodeV11 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___closed__1_value;
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__12);
v___x_30_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__16));
v___x_43_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5));
v___x_44_ = lean_array_push(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_45_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__17);
v___x_46_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__15));
v___x_47_ = lean_box(2);
v___x_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_45_);
return v___x_48_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__18);
v___x_50_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__13);
v___x_51_ = lean_array_push(v___x_50_, v___x_49_);
return v___x_51_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__19);
v___x_53_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__11));
v___x_54_ = lean_box(2);
v___x_55_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_52_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__20);
v___x_57_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5));
v___x_58_ = lean_array_push(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__21);
v___x_60_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__9));
v___x_61_ = lean_box(2);
v___x_62_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_59_);
return v___x_62_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__22);
v___x_64_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5));
v___x_65_ = lean_array_push(v___x_64_, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__23);
v___x_67_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__7));
v___x_68_ = lean_box(2);
v___x_69_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_66_);
return v___x_69_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__24);
v___x_71_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__5));
v___x_72_ = lean_array_push(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__25);
v___x_74_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__4));
v___x_75_ = lean_box(2);
v___x_76_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_73_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Chunk_instReprExtensionName_repr_spec__0(lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_nat_to_int(v_a_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(9u);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__0));
v___x_106_ = lean_string_length(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15, &l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15_once, _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__15);
v___x_108_ = lean_nat_to_int(v___x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg(lean_object* v_x_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_114_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5));
v___x_115_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6));
v___x_116_ = lean_obj_once(&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7, &l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7_once, _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7);
v___x_117_ = l_String_quote(v_x_113_);
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = 0;
v___x_121_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*1, v___x_120_);
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_115_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9));
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = lean_box(1);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__11));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_114_);
v___x_130_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_obj_once(&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16, &l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16_once, _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16);
v___x_133_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17));
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_131_);
v___x_135_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18));
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_132_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_120_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionName_repr(lean_object* v_x_139_, lean_object* v_prec_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_x_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___boxed(lean_object* v_x_142_, lean_object* v_prec_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Http_Chunk_instReprExtensionName_repr(v_x_142_, v_prec_143_);
lean_dec(v_prec_143_);
return v_res_144_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionName_decEq(lean_object* v_x_147_, lean_object* v_x_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_string_dec_eq(v_x_147_, v_x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionName_decEq___boxed(lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Std_Http_Chunk_instDecidableEqExtensionName_decEq(v_x_150_, v_x_151_);
lean_dec_ref(v_x_151_);
lean_dec_ref(v_x_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionName(lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_string_dec_eq(v_x_154_, v_x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionName___boxed(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = l_Std_Http_Chunk_instDecidableEqExtensionName(v_x_157_, v_x_158_);
lean_dec_ref(v_x_158_);
lean_dec_ref(v_x_157_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instBEqExtensionName_beq(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lean_string_dec_eq(v_x_161_, v_x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instBEqExtensionName_beq___boxed(lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_x_164_, v_x_165_);
lean_dec_ref(v_x_165_);
lean_dec_ref(v_x_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instToStringExtensionName___lam__0(lean_object* v_name_173_){
_start:
{
lean_inc_ref(v_name_173_);
return v_name_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instToStringExtensionName___lam__0___boxed(lean_object* v_name_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Http_Chunk_instToStringExtensionName___lam__0(v_name_174_);
lean_dec_ref(v_name_174_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x3f(lean_object* v_s_178_){
_start:
{
uint8_t v___x_179_; 
lean_inc_ref(v_s_178_);
v___x_179_ = l_Std_Http_Internal_isToken(v_s_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec_ref(v_s_178_);
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_s_178_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Chunk_ExtensionName_ofString_x21_spec__0(lean_object* v_msg_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__12));
v___x_184_ = lean_panic_fn_borrowed(v___x_183_, v_msg_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionName_ofString_x21(lean_object* v_s_188_){
_start:
{
lean_object* v___x_189_; 
lean_inc_ref(v_s_188_);
v___x_189_ = l_Std_Http_Chunk_ExtensionName_ofString_x3f(v_s_188_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_190_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0));
v___x_191_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__1));
v___x_192_ = lean_unsigned_to_nat(85u);
v___x_193_ = lean_unsigned_to_nat(12u);
v___x_194_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__2));
v___x_195_ = l_String_quote(v_s_188_);
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_197_ = l_mkPanicMessageWithDecl(v___x_190_, v___x_191_, v___x_192_, v___x_193_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = l_panic___at___00Std_Http_Chunk_ExtensionName_ofString_x21_spec__0(v___x_197_);
return v___x_198_;
}
else
{
lean_object* v_val_199_; 
lean_dec_ref(v_s_188_);
v_val_199_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_val_199_);
lean_dec_ref(v___x_189_);
return v_val_199_;
}
}
}
static lean_object* _init_l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26, &l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26_once, _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam___closed__26);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_205_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__5));
v___x_206_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__6));
v___x_207_ = lean_obj_once(&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7, &l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7_once, _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__7);
v___x_208_ = l_String_quote(v_x_204_);
v___x_209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___x_210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = 0;
v___x_212_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_211_);
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_206_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__9));
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = lean_box(1);
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionValue_repr___redArg___closed__1));
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_205_);
v___x_221_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__13));
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = lean_obj_once(&l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16, &l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16_once, _init_l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__16);
v___x_224_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__17));
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
lean_ctor_set(v___x_225_, 1, v___x_222_);
v___x_226_ = ((lean_object*)(l_Std_Http_Chunk_instReprExtensionName_repr___redArg___closed__18));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_223_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_211_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr(lean_object* v_x_230_, lean_object* v_prec_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_x_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___boxed(lean_object* v_x_233_, lean_object* v_prec_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Http_Chunk_instReprExtensionValue_repr(v_x_233_, v_prec_234_);
lean_dec(v_prec_234_);
return v_res_235_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = lean_string_dec_eq(v_x_238_, v_x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq___boxed(lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_Http_Chunk_instDecidableEqExtensionValue_decEq(v_x_241_, v_x_242_);
lean_dec_ref(v_x_242_);
lean_dec_ref(v_x_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instDecidableEqExtensionValue(lean_object* v_x_245_, lean_object* v_x_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = lean_string_dec_eq(v_x_245_, v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instDecidableEqExtensionValue___boxed(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Std_Http_Chunk_instDecidableEqExtensionValue(v_x_248_, v_x_249_);
lean_dec_ref(v_x_249_);
lean_dec_ref(v_x_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_instBEqExtensionValue_beq(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_string_dec_eq(v_x_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instBEqExtensionValue_beq___boxed(lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_x_255_, v_x_256_);
lean_dec_ref(v_x_256_);
lean_dec_ref(v_x_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_instToString___lam__0(lean_object* v_v_263_){
_start:
{
lean_inc_ref(v_v_263_);
return v_v_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_instToString___lam__0___boxed(lean_object* v_v_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Http_Chunk_ExtensionValue_instToString___lam__0(v_v_264_);
lean_dec_ref(v_v_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_quote(lean_object* v_s_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_Http_Internal_quoteHttpString___redArg(v_s_268_);
return v___x_269_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Chunk_ExtensionValue_ofString_x3f___lam__0(uint32_t v___y_270_){
_start:
{
uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_285_ = 9;
v___x_286_ = lean_uint32_dec_eq(v___y_270_, v___x_285_);
if (v___x_286_ == 0)
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = 32;
v___x_288_ = lean_uint32_dec_eq(v___y_270_, v___x_287_);
if (v___x_288_ == 0)
{
uint32_t v___x_289_; uint8_t v___x_290_; 
v___x_289_ = 33;
v___x_290_ = lean_uint32_dec_eq(v___y_270_, v___x_289_);
if (v___x_290_ == 0)
{
uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 35;
v___x_292_ = lean_uint32_dec_le(v___x_291_, v___y_270_);
if (v___x_292_ == 0)
{
goto v___jp_280_;
}
else
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 91;
v___x_294_ = lean_uint32_dec_le(v___y_270_, v___x_293_);
if (v___x_294_ == 0)
{
goto v___jp_280_;
}
else
{
return v___x_294_;
}
}
}
else
{
return v___x_290_;
}
}
else
{
return v___x_288_;
}
}
else
{
return v___x_286_;
}
v___jp_271_:
{
uint32_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 9;
v___x_273_ = lean_uint32_dec_eq(v___y_270_, v___x_272_);
if (v___x_273_ == 0)
{
uint32_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 32;
v___x_275_ = lean_uint32_dec_eq(v___y_270_, v___x_274_);
if (v___x_275_ == 0)
{
uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_276_ = 33;
v___x_277_ = lean_uint32_dec_le(v___x_276_, v___y_270_);
if (v___x_277_ == 0)
{
return v___x_277_;
}
else
{
uint32_t v___x_278_; uint8_t v___x_279_; 
v___x_278_ = 126;
v___x_279_ = lean_uint32_dec_le(v___y_270_, v___x_278_);
return v___x_279_;
}
}
else
{
return v___x_275_;
}
}
else
{
return v___x_273_;
}
}
v___jp_280_:
{
uint32_t v___x_281_; uint8_t v___x_282_; 
v___x_281_ = 93;
v___x_282_ = lean_uint32_dec_le(v___x_281_, v___y_270_);
if (v___x_282_ == 0)
{
goto v___jp_271_;
}
else
{
uint32_t v___x_283_; uint8_t v___x_284_; 
v___x_283_ = 126;
v___x_284_ = lean_uint32_dec_le(v___y_270_, v___x_283_);
if (v___x_284_ == 0)
{
goto v___jp_271_;
}
else
{
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f___lam__0___boxed(lean_object* v___y_295_){
_start:
{
uint32_t v___y_114__boxed_296_; uint8_t v_res_297_; lean_object* v_r_298_; 
v___y_114__boxed_296_ = lean_unbox_uint32(v___y_295_);
lean_dec(v___y_295_);
v_res_297_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f___lam__0(v___y_114__boxed_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object* v_s_300_){
_start:
{
lean_object* v___f_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___f_301_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x3f___closed__0));
lean_inc_ref(v_s_300_);
v___x_302_ = lean_string_data(v_s_300_);
v___x_303_ = l_List_all___redArg(v___x_302_, v___f_301_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec_ref(v_s_300_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_s_300_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(lean_object* v_msg_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___x_308_ = lean_panic_fn_borrowed(v___x_307_, v_msg_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x21(lean_object* v_s_311_){
_start:
{
lean_object* v___x_312_; 
lean_inc_ref(v_s_311_);
v___x_312_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_s_311_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_313_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0));
v___x_314_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0));
v___x_315_ = lean_unsigned_to_nat(152u);
v___x_316_ = lean_unsigned_to_nat(12u);
v___x_317_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1));
v___x_318_ = l_String_quote(v_s_311_);
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = l_mkPanicMessageWithDecl(v___x_313_, v___x_314_, v___x_315_, v___x_316_, v___x_319_);
lean_dec_ref(v___x_319_);
v___x_321_ = l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(v___x_320_);
return v___x_321_;
}
else
{
lean_object* v_val_322_; 
lean_dec_ref(v_s_311_);
v_val_322_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_322_);
lean_dec_ref(v___x_312_);
return v_val_322_;
}
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk_default___closed__1(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = ((lean_object*)(l_Std_Http_instInhabitedChunk_default___closed__0));
v___x_326_ = l_ByteArray_empty;
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk_default(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Std_Http_instInhabitedChunk_default___closed__1, &l_Std_Http_instInhabitedChunk_default___closed__1_once, _init_l_Std_Http_instInhabitedChunk_default___closed__1);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Std_Http_instInhabitedChunk_default;
return v___x_329_;
}
}
static lean_object* _init_l_Std_Http_Chunk_empty(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Std_Http_instInhabitedChunk_default___closed__1, &l_Std_Http_instInhabitedChunk_default___closed__1_once, _init_l_Std_Http_instInhabitedChunk_default___closed__1);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ofByteArray(lean_object* v_data_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l_Std_Http_instInhabitedChunk_default___closed__0));
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_data_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_insertExtension(lean_object* v_chunk_334_, lean_object* v_key_335_, lean_object* v_value_336_){
_start:
{
lean_object* v_data_337_; lean_object* v_extensions_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v_data_337_ = lean_ctor_get(v_chunk_334_, 0);
v_extensions_338_ = lean_ctor_get(v_chunk_334_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_chunk_334_);
if (v_isSharedCheck_348_ == 0)
{
v___x_340_ = v_chunk_334_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_extensions_338_);
lean_inc(v_data_337_);
lean_dec(v_chunk_334_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_value_336_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_key_335_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_array_push(v_extensions_338_, v___x_343_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_data_337_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_toString_x3f(lean_object* v_chunk_349_){
_start:
{
lean_object* v_data_350_; uint8_t v___x_351_; 
v_data_350_ = lean_ctor_get(v_chunk_349_, 0);
lean_inc_ref(v_data_350_);
lean_dec_ref(v_chunk_349_);
v___x_351_ = lean_string_validate_utf8(v_data_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v_data_350_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_string_from_utf8_unchecked(v_data_350_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0(lean_object* v_x1_355_, lean_object* v_x2_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_byte_array_size(v_x2_356_);
v___x_358_ = lean_nat_add(v_x1_355_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0___boxed(lean_object* v_x1_359_, lean_object* v_x2_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Http_Chunk_instEncodeV11___lam__0(v_x1_359_, v_x2_360_);
lean_dec_ref(v_x2_360_);
lean_dec(v_x1_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__1(lean_object* v_x1_364_, lean_object* v_x2_365_){
_start:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_fst_366_ = lean_ctor_get(v_x2_365_, 0);
lean_inc(v_fst_366_);
v_snd_367_ = lean_ctor_get(v_x2_365_, 1);
lean_inc(v_snd_367_);
lean_dec_ref(v_x2_365_);
v___x_368_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0));
v___x_369_ = lean_string_append(v_x1_364_, v___x_368_);
v___x_370_ = lean_string_append(v___x_369_, v_fst_366_);
lean_dec(v_fst_366_);
if (lean_obj_tag(v_snd_367_) == 0)
{
return v___x_370_;
}
else
{
lean_object* v_val_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_val_371_ = lean_ctor_get(v_snd_367_, 0);
lean_inc(v_val_371_);
lean_dec_ref(v_snd_367_);
v___x_372_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1));
v___x_373_ = l_Std_Http_Internal_quoteHttpString___redArg(v_val_371_);
v___x_374_ = lean_string_append(v___x_372_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = lean_string_append(v___x_370_, v___x_374_);
lean_dec_ref(v___x_374_);
return v___x_375_;
}
}
}
static lean_object* _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10));
v___x_397_ = lean_string_to_utf8(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2(lean_object* v___f_398_, lean_object* v___f_399_, lean_object* v___f_400_, lean_object* v_buffer_401_, lean_object* v_chunk_402_){
_start:
{
lean_object* v___y_404_; lean_object* v_data_418_; lean_object* v_extensions_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_475_; 
v_data_418_ = lean_ctor_get(v_chunk_402_, 0);
v_extensions_419_ = lean_ctor_get(v_chunk_402_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_chunk_402_);
if (v_isSharedCheck_475_ == 0)
{
v___x_421_ = v_chunk_402_;
v_isShared_422_ = v_isSharedCheck_475_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_extensions_419_);
lean_inc(v_data_418_);
lean_dec(v_chunk_402_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_475_;
goto v_resetjp_420_;
}
v___jp_403_:
{
lean_object* v_data_405_; lean_object* v_size_406_; lean_object* v_data_407_; lean_object* v_size_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
v_data_405_ = lean_ctor_get(v_buffer_401_, 0);
lean_inc_ref(v_data_405_);
v_size_406_ = lean_ctor_get(v_buffer_401_, 1);
lean_inc(v_size_406_);
lean_dec_ref(v_buffer_401_);
v_data_407_ = lean_ctor_get(v___y_404_, 0);
v_size_408_ = lean_ctor_get(v___y_404_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v___y_404_);
if (v_isSharedCheck_417_ == 0)
{
v___x_410_ = v___y_404_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_size_408_);
lean_inc(v_data_407_);
lean_dec(v___y_404_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = l_Array_append___redArg(v_data_405_, v_data_407_);
lean_dec_ref(v_data_407_);
v___x_413_ = lean_nat_add(v_size_406_, v_size_408_);
lean_dec(v_size_408_);
lean_dec(v_size_406_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v___x_413_);
lean_ctor_set(v___x_410_, 0, v___x_412_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
v_resetjp_420_:
{
lean_object* v_chunkLen_423_; lean_object* v___y_425_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_chunkLen_423_ = lean_byte_array_size(v_data_418_);
v___x_463_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_array_get_size(v_extensions_419_);
v___x_466_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_467_ = lean_nat_dec_lt(v___x_464_, v___x_465_);
if (v___x_467_ == 0)
{
lean_dec_ref(v_extensions_419_);
lean_dec_ref(v___f_400_);
v___y_425_ = v___x_463_;
goto v___jp_424_;
}
else
{
uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_le(v___x_465_, v___x_465_);
if (v___x_468_ == 0)
{
if (v___x_467_ == 0)
{
lean_dec_ref(v_extensions_419_);
lean_dec_ref(v___f_400_);
v___y_425_ = v___x_463_;
goto v___jp_424_;
}
else
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((size_t)0ULL);
v___x_470_ = lean_usize_of_nat(v___x_465_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_466_, v___f_400_, v_extensions_419_, v___x_469_, v___x_470_, v___x_463_);
v___y_425_ = v___x_471_;
goto v___jp_424_;
}
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_465_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_466_, v___f_400_, v_extensions_419_, v___x_472_, v___x_473_, v___x_463_);
v___y_425_ = v___x_474_;
goto v___jp_424_;
}
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; size_t v_sz_430_; size_t v___x_431_; lean_object* v___x_432_; lean_object* v_size_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_426_ = lean_unsigned_to_nat(16u);
v___x_427_ = l_Nat_toDigits(v___x_426_, v_chunkLen_423_);
v___x_428_ = lean_array_mk(v___x_427_);
v___x_429_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v_sz_430_ = lean_array_size(v___x_428_);
v___x_431_ = ((size_t)0ULL);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v___f_398_, v_sz_430_, v___x_431_, v___x_428_);
v_size_433_ = lean_byte_array_mk(v___x_432_);
v___x_434_ = lean_string_to_utf8(v___y_425_);
lean_dec_ref(v___y_425_);
v___x_435_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_436_ = lean_unsigned_to_nat(5u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_array_push(v___x_437_, v_size_433_);
v___x_439_ = lean_array_push(v___x_438_, v___x_434_);
v___x_440_ = lean_array_push(v___x_439_, v___x_435_);
v___x_441_ = lean_array_push(v___x_440_, v_data_418_);
v___x_442_ = lean_array_push(v___x_441_, v___x_435_);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_array_get_size(v___x_442_);
v___x_445_ = lean_nat_dec_lt(v___x_443_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v___f_399_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_443_);
lean_ctor_set(v___x_421_, 0, v___x_442_);
v___x_447_ = v___x_421_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_443_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v___y_404_ = v___x_447_;
goto v___jp_403_;
}
}
else
{
uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_le(v___x_444_, v___x_444_);
if (v___x_449_ == 0)
{
if (v___x_445_ == 0)
{
lean_object* v___x_451_; 
lean_dec_ref(v___f_399_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_443_);
lean_ctor_set(v___x_421_, 0, v___x_442_);
v___x_451_ = v___x_421_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_443_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
v___y_404_ = v___x_451_;
goto v___jp_403_;
}
}
else
{
size_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_453_ = lean_usize_of_nat(v___x_444_);
lean_inc_ref(v___x_442_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v___f_399_, v___x_442_, v___x_431_, v___x_453_, v___x_443_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_454_);
lean_ctor_set(v___x_421_, 0, v___x_442_);
v___x_456_ = v___x_421_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v___y_404_ = v___x_456_;
goto v___jp_403_;
}
}
}
else
{
size_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = lean_usize_of_nat(v___x_444_);
lean_inc_ref(v___x_442_);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v___f_399_, v___x_442_, v___x_431_, v___x_458_, v___x_443_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_459_);
lean_ctor_set(v___x_421_, 0, v___x_442_);
v___x_461_ = v___x_421_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
v___y_404_ = v___x_461_;
goto v___jp_403_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_instInhabitedTrailer_default(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_484_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedTrailer(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_485_;
}
}
static lean_object* _init_l_Std_Http_Trailer_empty(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_Http_Headers_empty;
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert___lam__0(lean_object* v_i_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_mk_empty_array_with_capacity(v___x_489_);
v___x_491_ = lean_array_push(v___x_490_, v_i_487_);
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
v_val_493_ = lean_ctor_get(v_x_488_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_501_ == 0)
{
v___x_495_ = v_x_488_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v_x_488_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_array_push(v_val_493_, v_i_487_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert(lean_object* v_trailer_503_, lean_object* v_name_504_, lean_object* v_value_505_){
_start:
{
lean_object* v_entries_506_; lean_object* v_indexes_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_521_; 
v_entries_506_ = lean_ctor_get(v_trailer_503_, 0);
v_indexes_507_ = lean_ctor_get(v_trailer_503_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_trailer_503_);
if (v_isSharedCheck_521_ == 0)
{
v___x_509_ = v_trailer_503_;
v_isShared_510_ = v_isSharedCheck_521_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_indexes_507_);
lean_inc(v_entries_506_);
lean_dec(v_trailer_503_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_521_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___f_511_; lean_object* v___f_512_; lean_object* v_i_513_; lean_object* v_f_514_; lean_object* v___x_515_; lean_object* v_entries_516_; lean_object* v_indexes_517_; lean_object* v___x_519_; 
v___f_511_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_512_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v_i_513_ = lean_array_get_size(v_entries_506_);
v_f_514_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_514_, 0, v_i_513_);
lean_inc_ref(v_name_504_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_name_504_);
lean_ctor_set(v___x_515_, 1, v_value_505_);
v_entries_516_ = lean_array_push(v_entries_506_, v___x_515_);
v_indexes_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_511_, v___f_512_, v_indexes_507_, v_name_504_, v_f_514_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_indexes_517_);
lean_ctor_set(v___x_509_, 0, v_entries_516_);
v___x_519_ = v___x_509_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_entries_516_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_indexes_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert_x21(lean_object* v_trailer_522_, lean_object* v_name_523_, lean_object* v_value_524_){
_start:
{
lean_object* v_entries_525_; lean_object* v_indexes_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_542_; 
v_entries_525_ = lean_ctor_get(v_trailer_522_, 0);
v_indexes_526_ = lean_ctor_get(v_trailer_522_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v_trailer_522_);
if (v_isSharedCheck_542_ == 0)
{
v___x_528_ = v_trailer_522_;
v_isShared_529_ = v_isSharedCheck_542_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_indexes_526_);
lean_inc(v_entries_525_);
lean_dec(v_trailer_522_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_542_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___f_532_; lean_object* v___f_533_; lean_object* v_i_534_; lean_object* v_f_535_; lean_object* v___x_536_; lean_object* v_entries_537_; lean_object* v_indexes_538_; lean_object* v___x_540_; 
v___x_530_ = l_Std_Http_Header_Name_ofString_x21(v_name_523_);
v___x_531_ = l_Std_Http_Header_Value_ofString_x21(v_value_524_);
v___f_532_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_533_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v_i_534_ = lean_array_get_size(v_entries_525_);
v_f_535_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_535_, 0, v_i_534_);
lean_inc_ref(v___x_530_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_530_);
lean_ctor_set(v___x_536_, 1, v___x_531_);
v_entries_537_ = lean_array_push(v_entries_525_, v___x_536_);
v_indexes_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_532_, v___f_533_, v_indexes_526_, v___x_530_, v_f_535_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v_indexes_538_);
lean_ctor_set(v___x_528_, 0, v_entries_537_);
v___x_540_ = v___x_528_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_entries_537_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_indexes_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f(lean_object* v_trailer_543_, lean_object* v_name_544_){
_start:
{
lean_object* v___f_545_; lean_object* v___f_546_; uint8_t v___x_547_; 
v___f_545_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_546_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_544_);
v___x_547_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_545_, v___f_546_, v_name_544_, v_trailer_543_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v_name_544_);
v___x_548_ = lean_box(0);
return v___x_548_;
}
else
{
lean_object* v_entries_549_; lean_object* v_indexes_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_entry_553_; lean_object* v___x_554_; lean_object* v_snd_555_; lean_object* v___x_556_; 
v_entries_549_ = lean_ctor_get(v_trailer_543_, 0);
v_indexes_550_ = lean_ctor_get(v_trailer_543_, 1);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_545_, v___f_546_, v_indexes_550_, v_name_544_);
v___x_552_ = lean_unsigned_to_nat(0u);
v_entry_553_ = lean_array_fget(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_array_fget_borrowed(v_entries_549_, v_entry_553_);
lean_dec(v_entry_553_);
v_snd_555_ = lean_ctor_get(v___x_554_, 1);
lean_inc(v_snd_555_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_snd_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f___boxed(lean_object* v_trailer_557_, lean_object* v_name_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Http_Trailer_get_x3f(v_trailer_557_, v_name_558_);
lean_dec_ref(v_trailer_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0(lean_object* v___x_560_, lean_object* v_entries_561_, lean_object* v_x1_562_, lean_object* v_x2_563_, lean_object* v_x3_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_snd_567_; 
v___x_565_ = lean_array_fget_borrowed(v___x_560_, v_x1_562_);
v___x_566_ = lean_array_fget_borrowed(v_entries_561_, v___x_565_);
v_snd_567_ = lean_ctor_get(v___x_566_, 1);
lean_inc(v_snd_567_);
return v_snd_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0___boxed(lean_object* v___x_568_, lean_object* v_entries_569_, lean_object* v_x1_570_, lean_object* v_x2_571_, lean_object* v_x3_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Http_Trailer_getAll_x3f___lam__0(v___x_568_, v_entries_569_, v_x1_570_, v_x2_571_, v_x3_572_);
lean_dec(v_x2_571_);
lean_dec(v_x1_570_);
lean_dec_ref(v_entries_569_);
lean_dec_ref(v___x_568_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f(lean_object* v_trailer_574_, lean_object* v_name_575_){
_start:
{
lean_object* v___f_576_; lean_object* v___f_577_; uint8_t v___x_578_; 
v___f_576_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_577_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_575_);
v___x_578_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_576_, v___f_577_, v_name_575_, v_trailer_574_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec_ref(v_name_575_);
lean_dec_ref(v_trailer_574_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_entries_580_; lean_object* v_indexes_581_; lean_object* v___x_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_entries_588_; lean_object* v___x_589_; 
v_entries_580_ = lean_ctor_get(v_trailer_574_, 0);
lean_inc_ref(v_entries_580_);
v_indexes_581_ = lean_ctor_get(v_trailer_574_, 1);
lean_inc_ref(v_indexes_581_);
lean_dec_ref(v_trailer_574_);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_576_, v___f_577_, v_indexes_581_, v_name_575_);
lean_dec_ref(v_indexes_581_);
lean_inc(v___x_582_);
v___f_583_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_getAll_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_583_, 0, v___x_582_);
lean_closure_set(v___f_583_, 1, v_entries_580_);
v___x_584_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_585_ = lean_array_get_size(v___x_582_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_mk_empty_array_with_capacity(v___x_585_);
v_entries_588_ = l_Array_mapFinIdxM_map___redArg(v___x_584_, v___x_582_, v___f_583_, v___x_585_, v___x_586_, v___x_587_);
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v_entries_588_);
return v___x_589_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Trailer_contains(lean_object* v_trailer_590_, lean_object* v_name_591_){
_start:
{
lean_object* v_indexes_592_; lean_object* v___f_593_; lean_object* v___f_594_; uint8_t v___x_595_; 
v_indexes_592_ = lean_ctor_get(v_trailer_590_, 1);
v___f_593_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_594_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_593_, v___f_594_, v_indexes_592_, v_name_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_contains___boxed(lean_object* v_trailer_596_, lean_object* v_name_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l_Std_Http_Trailer_contains(v_trailer_596_, v_name_597_);
lean_dec_ref(v_trailer_596_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1(lean_object* v___f_600_, lean_object* v___f_601_, lean_object* v_x1_602_, lean_object* v_x2_603_){
_start:
{
lean_object* v_fst_604_; lean_object* v_entries_605_; lean_object* v_indexes_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_617_; 
v_fst_604_ = lean_ctor_get(v_x2_603_, 0);
lean_inc(v_fst_604_);
v_entries_605_ = lean_ctor_get(v_x1_602_, 0);
v_indexes_606_ = lean_ctor_get(v_x1_602_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x1_602_);
if (v_isSharedCheck_617_ == 0)
{
v___x_608_ = v_x1_602_;
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_indexes_606_);
lean_inc(v_entries_605_);
lean_dec(v_x1_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_617_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_i_610_; lean_object* v_f_611_; lean_object* v_entries_612_; lean_object* v_indexes_613_; lean_object* v___x_615_; 
v_i_610_ = lean_array_get_size(v_entries_605_);
v_f_611_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_611_, 0, v_i_610_);
v_entries_612_ = lean_array_push(v_entries_605_, v_x2_603_);
v_indexes_613_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_600_, v___f_601_, v_indexes_606_, v_fst_604_, v_f_611_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v_indexes_613_);
lean_ctor_set(v___x_608_, 0, v_entries_612_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_entries_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_indexes_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__0(lean_object* v_name_618_, lean_object* v_x1_619_, lean_object* v_x2_620_){
_start:
{
lean_object* v_fst_621_; uint8_t v___x_622_; 
v_fst_621_ = lean_ctor_get(v_x2_620_, 0);
v___x_622_ = lean_string_dec_eq(v_fst_621_, v_name_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_array_push(v_x1_619_, v_x2_620_);
return v___x_623_;
}
else
{
lean_dec_ref(v_x2_620_);
return v_x1_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__0___boxed(lean_object* v_name_624_, lean_object* v_x1_625_, lean_object* v_x2_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Http_Trailer_erase___lam__0(v_name_624_, v_x1_625_, v_x2_626_);
lean_dec_ref(v_name_624_);
return v_res_627_;
}
}
static lean_object* _init_l_Std_Http_Trailer_erase___closed__1(void){
_start:
{
lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___x_633_; 
v___f_631_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v___f_632_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___x_633_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_632_, v___f_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase(lean_object* v_trailer_636_, lean_object* v_name_637_){
_start:
{
lean_object* v___f_638_; lean_object* v___f_639_; uint8_t v___x_640_; 
v___f_638_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_639_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_637_);
v___x_640_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_638_, v___f_639_, v_name_637_, v_trailer_636_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_name_637_);
return v_trailer_636_;
}
else
{
lean_object* v_entries_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___y_646_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_entries_641_ = lean_ctor_get(v_trailer_636_, 0);
lean_inc_ref(v_entries_641_);
lean_dec_ref(v_trailer_636_);
v___f_642_ = ((lean_object*)(l_Std_Http_Trailer_erase___closed__0));
v___x_643_ = lean_obj_once(&l_Std_Http_Trailer_erase___closed__1, &l_Std_Http_Trailer_erase___closed__1_once, _init_l_Std_Http_Trailer_erase___closed__1);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_entries_641_);
v___x_658_ = ((lean_object*)(l_Std_Http_Trailer_erase___closed__2));
v___x_659_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_660_ = lean_nat_dec_lt(v___x_644_, v___x_657_);
if (v___x_660_ == 0)
{
lean_dec_ref(v_entries_641_);
lean_dec_ref(v_name_637_);
v___y_646_ = v___x_658_;
goto v___jp_645_;
}
else
{
lean_object* v___f_661_; uint8_t v___x_662_; 
v___f_661_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_erase___lam__0___boxed), 3, 1);
lean_closure_set(v___f_661_, 0, v_name_637_);
v___x_662_ = lean_nat_dec_le(v___x_657_, v___x_657_);
if (v___x_662_ == 0)
{
if (v___x_660_ == 0)
{
lean_dec_ref(v___f_661_);
lean_dec_ref(v_entries_641_);
v___y_646_ = v___x_658_;
goto v___jp_645_;
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_657_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_659_, v___f_661_, v_entries_641_, v___x_663_, v___x_664_, v___x_658_);
v___y_646_ = v___x_665_;
goto v___jp_645_;
}
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_657_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_659_, v___f_661_, v_entries_641_, v___x_666_, v___x_667_, v___x_658_);
v___y_646_ = v___x_668_;
goto v___jp_645_;
}
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_array_get_size(v___y_646_);
v___x_648_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_649_ = lean_nat_dec_lt(v___x_644_, v___x_647_);
if (v___x_649_ == 0)
{
lean_dec_ref(v___y_646_);
return v___x_643_;
}
else
{
uint8_t v___x_650_; 
v___x_650_ = lean_nat_dec_le(v___x_647_, v___x_647_);
if (v___x_650_ == 0)
{
if (v___x_649_ == 0)
{
lean_dec_ref(v___y_646_);
return v___x_643_;
}
else
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_647_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_648_, v___f_642_, v___y_646_, v___x_651_, v___x_652_, v___x_643_);
return v___x_653_;
}
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_647_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_648_, v___f_642_, v___y_646_, v___x_654_, v___x_655_, v___x_643_);
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size(lean_object* v_trailer_669_){
_start:
{
lean_object* v_entries_670_; lean_object* v___x_671_; 
v_entries_670_ = lean_ctor_get(v_trailer_669_, 0);
v___x_671_ = lean_array_get_size(v_entries_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size___boxed(lean_object* v_trailer_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Http_Trailer_size(v_trailer_672_);
lean_dec_ref(v_trailer_672_);
return v_res_673_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Trailer_isEmpty(lean_object* v_trailer_674_){
_start:
{
lean_object* v_entries_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_entries_675_ = lean_ctor_get(v_trailer_674_, 0);
v___x_676_ = lean_array_get_size(v_entries_675_);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_nat_dec_eq(v___x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_isEmpty___boxed(lean_object* v_trailer_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Std_Http_Trailer_isEmpty(v_trailer_679_);
lean_dec_ref(v_trailer_679_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge(lean_object* v_t1_682_, lean_object* v_t2_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_Http_Headers_merge(v_t1_682_, v_t2_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge___boxed(lean_object* v_t1_685_, lean_object* v_t2_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Http_Trailer_merge(v_t1_685_, v_t2_686_);
lean_dec_ref(v_t2_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toList(lean_object* v_trailer_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Std_Http_Headers_toList(v_trailer_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray(lean_object* v_trailer_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_Http_Headers_toArray(v_trailer_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray___boxed(lean_object* v_trailer_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Http_Trailer_toArray(v_trailer_692_);
lean_dec_ref(v_trailer_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg(lean_object* v_trailer_694_, lean_object* v_init_695_, lean_object* v_f_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_Http_Headers_fold___redArg(v_trailer_694_, v_init_695_, v_f_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg___boxed(lean_object* v_trailer_698_, lean_object* v_init_699_, lean_object* v_f_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_Http_Trailer_fold___redArg(v_trailer_698_, v_init_699_, v_f_700_);
lean_dec_ref(v_trailer_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold(lean_object* v_00_u03b1_702_, lean_object* v_trailer_703_, lean_object* v_init_704_, lean_object* v_f_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_Http_Headers_fold___redArg(v_trailer_703_, v_init_704_, v_f_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___boxed(lean_object* v_00_u03b1_707_, lean_object* v_trailer_708_, lean_object* v_init_709_, lean_object* v_f_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_Http_Trailer_fold(v_00_u03b1_707_, v_trailer_708_, v_init_709_, v_f_710_);
lean_dec_ref(v_trailer_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0(lean_object* v___x_712_, lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v_name_715_, lean_object* v___x_716_, uint32_t v___x_717_, lean_object* v___x_718_, lean_object* v_it_719_, lean_object* v_acc_720_, lean_object* v_hP_721_, lean_object* v_recur_722_){
_start:
{
lean_object* v_it_724_; lean_object* v_out_725_; lean_object* v_it_741_; lean_object* v_startInclusive_742_; lean_object* v_endExclusive_743_; 
if (lean_obj_tag(v_it_719_) == 0)
{
lean_object* v_currPos_755_; lean_object* v_searcher_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_778_; 
v_currPos_755_ = lean_ctor_get(v_it_719_, 0);
v_searcher_756_ = lean_ctor_get(v_it_719_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_it_719_);
if (v_isSharedCheck_778_ == 0)
{
v___x_758_ = v_it_719_;
v_isShared_759_ = v_isSharedCheck_778_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_searcher_756_);
lean_inc(v_currPos_755_);
lean_dec(v_it_719_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_778_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_eq(v_searcher_756_, v___x_716_);
if (v___x_760_ == 0)
{
uint32_t v___x_761_; uint8_t v___x_762_; 
lean_dec(v___x_716_);
v___x_761_ = lean_string_utf8_get_fast(v_name_715_, v_searcher_756_);
v___x_762_ = lean_uint32_dec_eq(v___x_761_, v___x_717_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = lean_string_utf8_next_fast(v_name_715_, v_searcher_756_);
lean_dec(v_searcher_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_763_);
v___x_765_ = v___x_758_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_currPos_755_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_767_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; 
v___x_766_ = lean_apply_4(v_recur_722_, v___x_765_, v_acc_720_, lean_box(0), lean_box(0));
return v___x_766_;
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_slice_771_; lean_object* v_nextIt_773_; 
v___x_768_ = lean_string_utf8_next_fast(v_name_715_, v_searcher_756_);
v___x_769_ = lean_nat_sub(v___x_768_, v_searcher_756_);
v___x_770_ = lean_nat_add(v_searcher_756_, v___x_769_);
lean_dec(v___x_769_);
v_slice_771_ = l_String_Slice_subslice_x21(v___x_718_, v_currPos_755_, v_searcher_756_);
lean_inc(v___x_770_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_770_);
lean_ctor_set(v___x_758_, 0, v___x_770_);
v_nextIt_773_ = v___x_758_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v___x_770_);
v_nextIt_773_ = v_reuseFailAlloc_776_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v_startInclusive_774_; lean_object* v_endExclusive_775_; 
v_startInclusive_774_ = lean_ctor_get(v_slice_771_, 0);
lean_inc(v_startInclusive_774_);
v_endExclusive_775_ = lean_ctor_get(v_slice_771_, 1);
lean_inc(v_endExclusive_775_);
lean_dec_ref(v_slice_771_);
v_it_741_ = v_nextIt_773_;
v_startInclusive_742_ = v_startInclusive_774_;
v_endExclusive_743_ = v_endExclusive_775_;
goto v___jp_740_;
}
}
}
else
{
lean_object* v___x_777_; 
lean_del_object(v___x_758_);
lean_dec(v_searcher_756_);
v___x_777_ = lean_box(1);
v_it_741_ = v___x_777_;
v_startInclusive_742_ = v_currPos_755_;
v_endExclusive_743_ = v___x_716_;
goto v___jp_740_;
}
}
}
else
{
lean_dec_ref(v_recur_722_);
lean_dec(v___x_716_);
return v_acc_720_;
}
v___jp_723_:
{
if (lean_obj_tag(v_acc_720_) == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v_out_725_);
v___x_727_ = lean_apply_4(v_recur_722_, v_it_724_, v___x_726_, lean_box(0), lean_box(0));
return v___x_727_;
}
else
{
lean_object* v_val_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v_val_728_ = lean_ctor_get(v_acc_720_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_acc_720_);
if (v_isSharedCheck_739_ == 0)
{
v___x_730_ = v_acc_720_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_val_728_);
lean_dec(v_acc_720_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_732_ = lean_string_utf8_extract(v___x_712_, v___x_713_, v___x_714_);
v___x_733_ = lean_string_append(v_val_728_, v___x_732_);
lean_dec_ref(v___x_732_);
v___x_734_ = lean_string_append(v___x_733_, v_out_725_);
lean_dec_ref(v_out_725_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_738_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; 
v___x_737_ = lean_apply_4(v_recur_722_, v_it_724_, v___x_736_, lean_box(0), lean_box(0));
return v___x_737_;
}
}
}
}
v___jp_740_:
{
lean_object* v___x_744_; uint32_t v___x_745_; uint32_t v___x_746_; uint8_t v___x_747_; 
v___x_744_ = lean_string_utf8_extract(v_name_715_, v_startInclusive_742_, v_endExclusive_743_);
lean_dec(v_endExclusive_743_);
lean_dec(v_startInclusive_742_);
v___x_745_ = lean_string_utf8_get(v___x_744_, v___x_713_);
v___x_746_ = 97;
v___x_747_ = lean_uint32_dec_le(v___x_746_, v___x_745_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_string_utf8_set(v___x_744_, v___x_713_, v___x_745_);
v_it_724_ = v_it_741_;
v_out_725_ = v___x_748_;
goto v___jp_723_;
}
else
{
uint32_t v___x_749_; uint8_t v___x_750_; 
v___x_749_ = 122;
v___x_750_ = lean_uint32_dec_le(v___x_745_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
v___x_751_ = lean_string_utf8_set(v___x_744_, v___x_713_, v___x_745_);
v_it_724_ = v_it_741_;
v_out_725_ = v___x_751_;
goto v___jp_723_;
}
else
{
uint32_t v___x_752_; uint32_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = 4294967264;
v___x_753_ = lean_uint32_add(v___x_745_, v___x_752_);
v___x_754_ = lean_string_utf8_set(v___x_744_, v___x_713_, v___x_753_);
v_it_724_ = v_it_741_;
v_out_725_ = v___x_754_;
goto v___jp_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0___boxed(lean_object* v___x_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v_name_782_, lean_object* v___x_783_, lean_object* v___x_784_, lean_object* v___x_785_, lean_object* v_it_786_, lean_object* v_acc_787_, lean_object* v_hP_788_, lean_object* v_recur_789_){
_start:
{
uint32_t v___x_635__boxed_790_; lean_object* v_res_791_; 
v___x_635__boxed_790_ = lean_unbox_uint32(v___x_784_);
lean_dec(v___x_784_);
v_res_791_ = l_Std_Http_Trailer_instEncodeV11___lam__0(v___x_779_, v___x_780_, v___x_781_, v_name_782_, v___x_783_, v___x_635__boxed_790_, v___x_785_, v_it_786_, v_acc_787_, v_hP_788_, v_recur_789_);
lean_dec_ref(v___x_785_);
lean_dec_ref(v_name_782_);
lean_dec(v___x_781_);
lean_dec(v___x_780_);
lean_dec_ref(v___x_779_);
return v_res_791_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2));
v___x_796_ = lean_string_utf8_byte_size(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_797_; lean_object* v___x_798_; 
v___x_797_ = 45;
v___x_798_ = lean_box_uint32(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1(lean_object* v_buf_799_, lean_object* v_name_800_, lean_object* v_value_801_){
_start:
{
lean_object* v___y_803_; lean_object* v___f_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_it_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___f_822_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1));
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = lean_string_utf8_byte_size(v_name_800_);
lean_inc_ref(v_name_800_);
v___x_825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_825_, 0, v_name_800_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
lean_inc_ref(v___x_825_);
v_it_826_ = l_String_Slice_splitToSubslice___redArg(v___x_825_, v___f_822_);
v___x_827_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2));
v___x_828_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3, &l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3);
v___x_829_ = l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1;
v___f_830_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_830_, 0, v___x_827_);
lean_closure_set(v___f_830_, 1, v___x_823_);
lean_closure_set(v___f_830_, 2, v___x_828_);
lean_closure_set(v___f_830_, 3, v_name_800_);
lean_closure_set(v___f_830_, 4, v___x_824_);
lean_closure_set(v___f_830_, 5, v___x_829_);
lean_closure_set(v___f_830_, 6, v___x_825_);
v___x_831_ = lean_box(0);
v___x_832_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_830_, v_it_826_, v___x_831_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___y_803_ = v___x_833_;
goto v___jp_802_;
}
else
{
lean_object* v_val_834_; 
v_val_834_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_val_834_);
lean_dec_ref(v___x_832_);
v___y_803_ = v_val_834_;
goto v___jp_802_;
}
v___jp_802_:
{
lean_object* v_data_804_; lean_object* v_size_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_821_; 
v_data_804_ = lean_ctor_get(v_buf_799_, 0);
v_size_805_ = lean_ctor_get(v_buf_799_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_buf_799_);
if (v_isSharedCheck_821_ == 0)
{
v___x_807_ = v_buf_799_;
v_isShared_808_ = v_isSharedCheck_821_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_size_805_);
lean_inc(v_data_804_);
lean_dec(v_buf_799_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_821_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_809_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0));
v___x_810_ = lean_string_append(v___y_803_, v___x_809_);
v___x_811_ = lean_string_append(v___x_810_, v_value_801_);
v___x_812_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10));
v___x_813_ = lean_string_append(v___x_811_, v___x_812_);
v___x_814_ = lean_string_to_utf8(v___x_813_);
lean_dec_ref(v___x_813_);
lean_inc_ref(v___x_814_);
v___x_815_ = lean_array_push(v_data_804_, v___x_814_);
v___x_816_ = lean_byte_array_size(v___x_814_);
lean_dec_ref(v___x_814_);
v___x_817_ = lean_nat_add(v_size_805_, v___x_816_);
lean_dec(v_size_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_817_);
lean_ctor_set(v___x_807_, 0, v___x_815_);
v___x_819_ = v___x_807_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___boxed(lean_object* v_buf_835_, lean_object* v_name_836_, lean_object* v_value_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_Http_Trailer_instEncodeV11___lam__1(v_buf_835_, v_name_836_, v_value_837_);
lean_dec_ref(v_value_837_);
return v_res_838_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0));
v___x_841_ = lean_string_to_utf8(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1);
v___x_843_ = lean_byte_array_size(v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_845_ = lean_byte_array_size(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2(lean_object* v___f_846_, lean_object* v_buffer_847_, lean_object* v_trailer_848_){
_start:
{
lean_object* v_data_849_; lean_object* v_size_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_875_; 
v_data_849_ = lean_ctor_get(v_buffer_847_, 0);
v_size_850_ = lean_ctor_get(v_buffer_847_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_buffer_847_);
if (v_isSharedCheck_875_ == 0)
{
v___x_852_ = v_buffer_847_;
v_isShared_853_ = v_isSharedCheck_875_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_size_850_);
lean_inc(v_data_849_);
lean_dec(v_buffer_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_875_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_854_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1);
v___x_855_ = lean_array_push(v_data_849_, v___x_854_);
v___x_856_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2);
v___x_857_ = lean_nat_add(v_size_850_, v___x_856_);
lean_dec(v_size_850_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_857_);
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_859_ = v___x_852_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_874_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v_data_861_; lean_object* v_size_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_873_; 
v___x_860_ = l_Std_Http_Headers_fold___redArg(v_trailer_848_, v___x_859_, v___f_846_);
v_data_861_ = lean_ctor_get(v___x_860_, 0);
v_size_862_ = lean_ctor_get(v___x_860_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_864_ = v___x_860_;
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_size_862_);
lean_inc(v_data_861_);
lean_dec(v___x_860_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_873_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_866_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_867_ = lean_array_push(v_data_861_, v___x_866_);
v___x_868_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3);
v___x_869_ = lean_nat_add(v_size_862_, v___x_868_);
lean_dec(v_size_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v___x_869_);
lean_ctor_set(v___x_864_, 0, v___x_867_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___boxed(lean_object* v___f_876_, lean_object* v_buffer_877_, lean_object* v_trailer_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_Http_Trailer_instEncodeV11___lam__2(v___f_876_, v_buffer_877_, v_trailer_878_);
lean_dec_ref(v_trailer_878_);
return v_res_879_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Chunk(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instInhabitedChunk_default = _init_l_Std_Http_instInhabitedChunk_default();
lean_mark_persistent(l_Std_Http_instInhabitedChunk_default);
l_Std_Http_instInhabitedChunk = _init_l_Std_Http_instInhabitedChunk();
lean_mark_persistent(l_Std_Http_instInhabitedChunk);
l_Std_Http_Chunk_empty = _init_l_Std_Http_Chunk_empty();
lean_mark_persistent(l_Std_Http_Chunk_empty);
l_Std_Http_instInhabitedTrailer_default = _init_l_Std_Http_instInhabitedTrailer_default();
lean_mark_persistent(l_Std_Http_instInhabitedTrailer_default);
l_Std_Http_instInhabitedTrailer = _init_l_Std_Http_instInhabitedTrailer();
lean_mark_persistent(l_Std_Http_instInhabitedTrailer);
l_Std_Http_Trailer_empty = _init_l_Std_Http_Trailer_empty();
lean_mark_persistent(l_Std_Http_Trailer_empty);
l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1 = _init_l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1();
lean_mark_persistent(l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Internal_Http_Internal_String(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Chunk(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Internal_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam = _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam();
lean_mark_persistent(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam);
l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam = _init_l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam();
lean_mark_persistent(l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Headers(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Internal_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Chunk(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Chunk(builtin);
}
#ifdef __cplusplus
}
#endif
