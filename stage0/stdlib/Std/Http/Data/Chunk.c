// Lean compiler output
// Module: Std.Http.Data.Chunk
// Imports: public import Std.Http.Internal public import Std.Http.Data.Headers public meta import Std.Http.Internal.String
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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_quoteHttpString___redArg(lean_object*);
lean_object* l_UInt32_toUInt8___boxed(lean_object*);
extern lean_object* l_Std_Http_Headers_empty;
lean_object* l_Std_Http_Header_Name_ofString_x21(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
static const lean_string_object l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.Http.Data.Chunk"};
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Trailer_erase___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Trailer_erase___closed__0;
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
lean_dec_ref_known(v___x_189_, 1);
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
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 1;
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v_tail_273_; uint8_t v___y_275_; uint32_t v___x_277_; uint32_t v___x_278_; uint8_t v___x_279_; 
v_head_272_ = lean_ctor_get(v_x_270_, 0);
v_tail_273_ = lean_ctor_get(v_x_270_, 1);
v___x_277_ = 9;
v___x_278_ = lean_unbox_uint32(v_head_272_);
v___x_279_ = lean_uint32_dec_eq(v___x_278_, v___x_277_);
if (v___x_279_ == 0)
{
uint32_t v___x_280_; uint32_t v___x_281_; uint8_t v___x_282_; 
v___x_280_ = 32;
v___x_281_ = lean_unbox_uint32(v_head_272_);
v___x_282_ = lean_uint32_dec_eq(v___x_281_, v___x_280_);
if (v___x_282_ == 0)
{
uint32_t v___x_283_; uint8_t v___y_285_; uint8_t v___y_286_; uint8_t v___y_291_; uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_283_ = 33;
v___x_299_ = lean_unbox_uint32(v_head_272_);
v___x_300_ = lean_uint32_dec_eq(v___x_299_, v___x_283_);
if (v___x_300_ == 0)
{
uint32_t v___x_301_; uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_301_ = 35;
v___x_302_ = lean_unbox_uint32(v_head_272_);
v___x_303_ = lean_uint32_dec_le(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
else
{
uint32_t v___x_304_; uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_304_ = 91;
v___x_305_ = lean_unbox_uint32(v_head_272_);
v___x_306_ = lean_uint32_dec_le(v___x_305_, v___x_304_);
v___y_291_ = v___x_306_;
goto v___jp_290_;
}
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
v___jp_284_:
{
if (v___y_286_ == 0)
{
uint32_t v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unbox_uint32(v_head_272_);
v___x_288_ = lean_uint32_dec_le(v___x_283_, v___x_287_);
if (v___x_288_ == 0)
{
v___y_275_ = v___x_288_;
goto v___jp_274_;
}
else
{
v___y_275_ = v___y_285_;
goto v___jp_274_;
}
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
}
v___jp_290_:
{
if (v___y_291_ == 0)
{
uint32_t v___x_292_; uint32_t v___x_293_; uint8_t v___x_294_; uint32_t v___x_295_; uint32_t v___x_296_; uint8_t v___x_297_; 
v___x_292_ = 93;
v___x_293_ = lean_unbox_uint32(v_head_272_);
v___x_294_ = lean_uint32_dec_le(v___x_292_, v___x_293_);
v___x_295_ = 126;
v___x_296_ = lean_unbox_uint32(v_head_272_);
v___x_297_ = lean_uint32_dec_le(v___x_296_, v___x_295_);
if (v___x_294_ == 0)
{
v___y_285_ = v___x_297_;
v___y_286_ = v___x_294_;
goto v___jp_284_;
}
else
{
v___y_285_ = v___x_297_;
v___y_286_ = v___x_297_;
goto v___jp_284_;
}
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
}
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
v___jp_274_:
{
if (v___y_275_ == 0)
{
return v___y_275_;
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0___boxed(lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(v_x_310_);
lean_dec(v_x_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object* v_s_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
lean_inc_ref(v_s_313_);
v___x_314_ = lean_string_data(v_s_313_);
v___x_315_ = l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(v___x_314_);
lean_dec(v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v_s_313_);
v___x_316_ = lean_box(0);
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_s_313_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(lean_object* v_msg_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___x_320_ = lean_panic_fn_borrowed(v___x_319_, v_msg_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x21(lean_object* v_s_323_){
_start:
{
lean_object* v___x_324_; 
lean_inc_ref(v_s_323_);
v___x_324_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_s_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_325_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0));
v___x_326_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0));
v___x_327_ = lean_unsigned_to_nat(152u);
v___x_328_ = lean_unsigned_to_nat(12u);
v___x_329_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1));
v___x_330_ = l_String_quote(v_s_323_);
v___x_331_ = lean_string_append(v___x_329_, v___x_330_);
lean_dec_ref(v___x_330_);
v___x_332_ = l_mkPanicMessageWithDecl(v___x_325_, v___x_326_, v___x_327_, v___x_328_, v___x_331_);
lean_dec_ref(v___x_331_);
v___x_333_ = l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(v___x_332_);
return v___x_333_;
}
else
{
lean_object* v_val_334_; 
lean_dec_ref(v_s_323_);
v_val_334_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_334_);
lean_dec_ref_known(v___x_324_, 1);
return v_val_334_;
}
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk_default___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = ((lean_object*)(l_Std_Http_instInhabitedChunk_default___closed__0));
v___x_338_ = l_ByteArray_empty;
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk_default(void){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_obj_once(&l_Std_Http_instInhabitedChunk_default___closed__1, &l_Std_Http_instInhabitedChunk_default___closed__1_once, _init_l_Std_Http_instInhabitedChunk_default___closed__1);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_Http_instInhabitedChunk_default;
return v___x_341_;
}
}
static lean_object* _init_l_Std_Http_Chunk_empty(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Std_Http_instInhabitedChunk_default___closed__1, &l_Std_Http_instInhabitedChunk_default___closed__1_once, _init_l_Std_Http_instInhabitedChunk_default___closed__1);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ofByteArray(lean_object* v_data_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l_Std_Http_instInhabitedChunk_default___closed__0));
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_data_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_insertExtension(lean_object* v_chunk_346_, lean_object* v_key_347_, lean_object* v_value_348_){
_start:
{
lean_object* v_data_349_; lean_object* v_extensions_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_360_; 
v_data_349_ = lean_ctor_get(v_chunk_346_, 0);
v_extensions_350_ = lean_ctor_get(v_chunk_346_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_chunk_346_);
if (v_isSharedCheck_360_ == 0)
{
v___x_352_ = v_chunk_346_;
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_extensions_350_);
lean_inc(v_data_349_);
lean_dec(v_chunk_346_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_value_348_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_key_347_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_array_push(v_extensions_350_, v___x_355_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_356_);
v___x_358_ = v___x_352_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_data_349_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_toString_x3f(lean_object* v_chunk_361_){
_start:
{
lean_object* v_data_362_; uint8_t v___x_363_; 
v_data_362_ = lean_ctor_get(v_chunk_361_, 0);
lean_inc_ref(v_data_362_);
lean_dec_ref(v_chunk_361_);
v___x_363_ = lean_string_validate_utf8(v_data_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v_data_362_);
v___x_364_ = lean_box(0);
return v___x_364_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_string_from_utf8_unchecked(v_data_362_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0(lean_object* v_x1_367_, lean_object* v_x2_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_byte_array_size(v_x2_368_);
v___x_370_ = lean_nat_add(v_x1_367_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0___boxed(lean_object* v_x1_371_, lean_object* v_x2_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Http_Chunk_instEncodeV11___lam__0(v_x1_371_, v_x2_372_);
lean_dec_ref(v_x2_372_);
lean_dec(v_x1_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__1(lean_object* v_x1_376_, lean_object* v_x2_377_){
_start:
{
lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_fst_378_ = lean_ctor_get(v_x2_377_, 0);
lean_inc(v_fst_378_);
v_snd_379_ = lean_ctor_get(v_x2_377_, 1);
lean_inc(v_snd_379_);
lean_dec_ref(v_x2_377_);
v___x_380_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0));
v___x_381_ = lean_string_append(v_x1_376_, v___x_380_);
v___x_382_ = lean_string_append(v___x_381_, v_fst_378_);
lean_dec(v_fst_378_);
if (lean_obj_tag(v_snd_379_) == 0)
{
return v___x_382_;
}
else
{
lean_object* v_val_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_val_383_ = lean_ctor_get(v_snd_379_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_snd_379_, 1);
v___x_384_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1));
v___x_385_ = l_Std_Http_Internal_quoteHttpString___redArg(v_val_383_);
v___x_386_ = lean_string_append(v___x_384_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = lean_string_append(v___x_382_, v___x_386_);
lean_dec_ref(v___x_386_);
return v___x_387_;
}
}
}
static lean_object* _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10));
v___x_409_ = lean_string_to_utf8(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2(lean_object* v___f_410_, lean_object* v___f_411_, lean_object* v___f_412_, lean_object* v_buffer_413_, lean_object* v_chunk_414_){
_start:
{
lean_object* v___y_416_; lean_object* v_data_430_; lean_object* v_extensions_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_478_; 
v_data_430_ = lean_ctor_get(v_chunk_414_, 0);
v_extensions_431_ = lean_ctor_get(v_chunk_414_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_chunk_414_);
if (v_isSharedCheck_478_ == 0)
{
v___x_433_ = v_chunk_414_;
v_isShared_434_ = v_isSharedCheck_478_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_extensions_431_);
lean_inc(v_data_430_);
lean_dec(v_chunk_414_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_478_;
goto v_resetjp_432_;
}
v___jp_415_:
{
lean_object* v_data_417_; lean_object* v_size_418_; lean_object* v_data_419_; lean_object* v_size_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_429_; 
v_data_417_ = lean_ctor_get(v_buffer_413_, 0);
lean_inc_ref(v_data_417_);
v_size_418_ = lean_ctor_get(v_buffer_413_, 1);
lean_inc(v_size_418_);
lean_dec_ref(v_buffer_413_);
v_data_419_ = lean_ctor_get(v___y_416_, 0);
v_size_420_ = lean_ctor_get(v___y_416_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v___y_416_);
if (v_isSharedCheck_429_ == 0)
{
v___x_422_ = v___y_416_;
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_size_420_);
lean_inc(v_data_419_);
lean_dec(v___y_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_424_ = l_Array_append___redArg(v_data_417_, v_data_419_);
lean_dec_ref(v_data_419_);
v___x_425_ = lean_nat_add(v_size_418_, v_size_420_);
lean_dec(v_size_420_);
lean_dec(v_size_418_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v___x_425_);
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_427_ = v___x_422_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
v_resetjp_432_:
{
lean_object* v_chunkLen_435_; lean_object* v___y_437_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_chunkLen_435_ = lean_byte_array_size(v_data_430_);
v___x_466_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = lean_array_get_size(v_extensions_431_);
v___x_469_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_470_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_470_ == 0)
{
lean_dec_ref(v_extensions_431_);
lean_dec_ref(v___f_412_);
v___y_437_ = v___x_466_;
goto v___jp_436_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = lean_nat_dec_le(v___x_468_, v___x_468_);
if (v___x_471_ == 0)
{
if (v___x_470_ == 0)
{
lean_dec_ref(v_extensions_431_);
lean_dec_ref(v___f_412_);
v___y_437_ = v___x_466_;
goto v___jp_436_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_468_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_469_, v___f_412_, v_extensions_431_, v___x_472_, v___x_473_, v___x_466_);
v___y_437_ = v___x_474_;
goto v___jp_436_;
}
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((size_t)0ULL);
v___x_476_ = lean_usize_of_nat(v___x_468_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_469_, v___f_412_, v_extensions_431_, v___x_475_, v___x_476_, v___x_466_);
v___y_437_ = v___x_477_;
goto v___jp_436_;
}
}
v___jp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; size_t v_sz_442_; size_t v___x_443_; lean_object* v___x_444_; lean_object* v_size_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_438_ = lean_unsigned_to_nat(16u);
v___x_439_ = l_Nat_toDigits(v___x_438_, v_chunkLen_435_);
v___x_440_ = lean_array_mk(v___x_439_);
v___x_441_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v_sz_442_ = lean_array_size(v___x_440_);
v___x_443_ = ((size_t)0ULL);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_441_, v___f_410_, v_sz_442_, v___x_443_, v___x_440_);
v_size_445_ = lean_byte_array_mk(v___x_444_);
v___x_446_ = lean_string_to_utf8(v___y_437_);
lean_dec_ref(v___y_437_);
v___x_447_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_448_ = lean_unsigned_to_nat(5u);
v___x_449_ = lean_mk_empty_array_with_capacity(v___x_448_);
v___x_450_ = lean_array_push(v___x_449_, v_size_445_);
v___x_451_ = lean_array_push(v___x_450_, v___x_446_);
v___x_452_ = lean_array_push(v___x_451_, v___x_447_);
v___x_453_ = lean_array_push(v___x_452_, v_data_430_);
v___x_454_ = lean_array_push(v___x_453_, v___x_447_);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_array_get_size(v___x_454_);
v___x_457_ = lean_nat_dec_lt(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_459_; 
lean_dec_ref(v___f_411_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_455_);
lean_ctor_set(v___x_433_, 0, v___x_454_);
v___x_459_ = v___x_433_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_455_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_416_ = v___x_459_;
goto v___jp_415_;
}
}
else
{
size_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = lean_usize_of_nat(v___x_456_);
lean_inc_ref(v___x_454_);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_441_, v___f_411_, v___x_454_, v___x_443_, v___x_461_, v___x_455_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_462_);
lean_ctor_set(v___x_433_, 0, v___x_454_);
v___x_464_ = v___x_433_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v___y_416_ = v___x_464_;
goto v___jp_415_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_instInhabitedTrailer_default(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_487_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedTrailer(void){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_488_;
}
}
static lean_object* _init_l_Std_Http_Trailer_empty(void){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_Http_Headers_empty;
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert___lam__0(lean_object* v_i_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_492_);
v___x_494_ = lean_array_push(v___x_493_, v_i_490_);
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_val_496_ = lean_ctor_get(v_x_491_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_x_491_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v_x_491_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_x_491_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_array_push(v_val_496_, v_i_490_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert(lean_object* v_trailer_506_, lean_object* v_name_507_, lean_object* v_value_508_){
_start:
{
lean_object* v_entries_509_; lean_object* v_indexes_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_524_; 
v_entries_509_ = lean_ctor_get(v_trailer_506_, 0);
v_indexes_510_ = lean_ctor_get(v_trailer_506_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_trailer_506_);
if (v_isSharedCheck_524_ == 0)
{
v___x_512_ = v_trailer_506_;
v_isShared_513_ = v_isSharedCheck_524_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_indexes_510_);
lean_inc(v_entries_509_);
lean_dec(v_trailer_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_524_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v_i_516_; lean_object* v_f_517_; lean_object* v___x_518_; lean_object* v_entries_519_; lean_object* v_indexes_520_; lean_object* v___x_522_; 
v___f_514_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_515_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v_i_516_ = lean_array_get_size(v_entries_509_);
v_f_517_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_517_, 0, v_i_516_);
lean_inc_ref(v_name_507_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_name_507_);
lean_ctor_set(v___x_518_, 1, v_value_508_);
v_entries_519_ = lean_array_push(v_entries_509_, v___x_518_);
v_indexes_520_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_514_, v___f_515_, v_indexes_510_, v_name_507_, v_f_517_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_indexes_520_);
lean_ctor_set(v___x_512_, 0, v_entries_519_);
v___x_522_ = v___x_512_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_entries_519_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_indexes_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert_x21(lean_object* v_trailer_525_, lean_object* v_name_526_, lean_object* v_value_527_){
_start:
{
lean_object* v_entries_528_; lean_object* v_indexes_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_545_; 
v_entries_528_ = lean_ctor_get(v_trailer_525_, 0);
v_indexes_529_ = lean_ctor_get(v_trailer_525_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_trailer_525_);
if (v_isSharedCheck_545_ == 0)
{
v___x_531_ = v_trailer_525_;
v_isShared_532_ = v_isSharedCheck_545_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_indexes_529_);
lean_inc(v_entries_528_);
lean_dec(v_trailer_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_545_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v_i_537_; lean_object* v_f_538_; lean_object* v___x_539_; lean_object* v_entries_540_; lean_object* v_indexes_541_; lean_object* v___x_543_; 
v___x_533_ = l_Std_Http_Header_Name_ofString_x21(v_name_526_);
v___x_534_ = l_Std_Http_Header_Value_ofString_x21(v_value_527_);
v___f_535_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_536_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v_i_537_ = lean_array_get_size(v_entries_528_);
v_f_538_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_538_, 0, v_i_537_);
lean_inc_ref(v___x_533_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_533_);
lean_ctor_set(v___x_539_, 1, v___x_534_);
v_entries_540_ = lean_array_push(v_entries_528_, v___x_539_);
v_indexes_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_535_, v___f_536_, v_indexes_529_, v___x_533_, v_f_538_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v_indexes_541_);
lean_ctor_set(v___x_531_, 0, v_entries_540_);
v___x_543_ = v___x_531_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_entries_540_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v_indexes_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f(lean_object* v_trailer_546_, lean_object* v_name_547_){
_start:
{
lean_object* v_entries_548_; lean_object* v_indexes_549_; lean_object* v___f_550_; lean_object* v___f_551_; uint8_t v___x_552_; 
v_entries_548_ = lean_ctor_get(v_trailer_546_, 0);
v_indexes_549_ = lean_ctor_get(v_trailer_546_, 1);
v___f_550_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_551_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_547_);
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_550_, v___f_551_, v_indexes_549_, v_name_547_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v_name_547_);
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_entry_556_; lean_object* v___x_557_; lean_object* v_snd_558_; lean_object* v___x_559_; 
v___x_554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_550_, v___f_551_, v_indexes_549_, v_name_547_);
v___x_555_ = lean_unsigned_to_nat(0u);
v_entry_556_ = lean_array_fget(v___x_554_, v___x_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_array_fget_borrowed(v_entries_548_, v_entry_556_);
lean_dec(v_entry_556_);
v_snd_558_ = lean_ctor_get(v___x_557_, 1);
lean_inc(v_snd_558_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_snd_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f___boxed(lean_object* v_trailer_560_, lean_object* v_name_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Http_Trailer_get_x3f(v_trailer_560_, v_name_561_);
lean_dec_ref(v_trailer_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0(lean_object* v___x_563_, lean_object* v_entries_564_, lean_object* v_x1_565_, lean_object* v_x2_566_, lean_object* v_x3_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_snd_570_; 
v___x_568_ = lean_array_fget_borrowed(v___x_563_, v_x1_565_);
v___x_569_ = lean_array_fget_borrowed(v_entries_564_, v___x_568_);
v_snd_570_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_snd_570_);
return v_snd_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0___boxed(lean_object* v___x_571_, lean_object* v_entries_572_, lean_object* v_x1_573_, lean_object* v_x2_574_, lean_object* v_x3_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_Http_Trailer_getAll_x3f___lam__0(v___x_571_, v_entries_572_, v_x1_573_, v_x2_574_, v_x3_575_);
lean_dec(v_x2_574_);
lean_dec(v_x1_573_);
lean_dec_ref(v_entries_572_);
lean_dec_ref(v___x_571_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f(lean_object* v_trailer_577_, lean_object* v_name_578_){
_start:
{
lean_object* v_entries_579_; lean_object* v_indexes_580_; lean_object* v___f_581_; lean_object* v___f_582_; uint8_t v___x_583_; 
v_entries_579_ = lean_ctor_get(v_trailer_577_, 0);
lean_inc_ref(v_entries_579_);
v_indexes_580_ = lean_ctor_get(v_trailer_577_, 1);
lean_inc_ref(v_indexes_580_);
lean_dec_ref(v_trailer_577_);
v___f_581_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_582_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_578_);
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_581_, v___f_582_, v_indexes_580_, v_name_578_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_dec_ref(v_indexes_580_);
lean_dec_ref(v_entries_579_);
lean_dec_ref(v_name_578_);
v___x_584_ = lean_box(0);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v_entries_590_; lean_object* v___x_591_; 
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_581_, v___f_582_, v_indexes_580_, v_name_578_);
lean_dec_ref(v_indexes_580_);
lean_inc_n(v___x_585_, 2);
v___f_586_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_getAll_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_586_, 0, v___x_585_);
lean_closure_set(v___f_586_, 1, v_entries_579_);
v___x_587_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v_sz_588_ = lean_array_size(v___x_585_);
v___x_589_ = ((size_t)0ULL);
v_entries_590_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_587_, v___x_585_, v___f_586_, v_sz_588_, v___x_589_, v___x_585_);
lean_dec(v___x_585_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_entries_590_);
return v___x_591_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Trailer_contains(lean_object* v_trailer_592_, lean_object* v_name_593_){
_start:
{
lean_object* v_indexes_594_; lean_object* v___f_595_; lean_object* v___f_596_; uint8_t v___x_597_; 
v_indexes_594_ = lean_ctor_get(v_trailer_592_, 1);
v___f_595_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_596_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_595_, v___f_596_, v_indexes_594_, v_name_593_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_contains___boxed(lean_object* v_trailer_598_, lean_object* v_name_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Std_Http_Trailer_contains(v_trailer_598_, v_name_599_);
lean_dec_ref(v_trailer_598_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1(lean_object* v_name_602_, lean_object* v___f_603_, lean_object* v___f_604_, lean_object* v_x1_605_, lean_object* v_x2_606_){
_start:
{
lean_object* v_fst_607_; uint8_t v___x_608_; 
v_fst_607_ = lean_ctor_get(v_x2_606_, 0);
lean_inc(v_fst_607_);
v___x_608_ = lean_string_dec_eq(v_name_602_, v_fst_607_);
if (v___x_608_ == 0)
{
lean_object* v_entries_609_; lean_object* v_indexes_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_621_; 
v_entries_609_ = lean_ctor_get(v_x1_605_, 0);
v_indexes_610_ = lean_ctor_get(v_x1_605_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_x1_605_);
if (v_isSharedCheck_621_ == 0)
{
v___x_612_ = v_x1_605_;
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_indexes_610_);
lean_inc(v_entries_609_);
lean_dec(v_x1_605_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_i_614_; lean_object* v_f_615_; lean_object* v_entries_616_; lean_object* v_indexes_617_; lean_object* v___x_619_; 
v_i_614_ = lean_array_get_size(v_entries_609_);
v_f_615_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_615_, 0, v_i_614_);
v_entries_616_ = lean_array_push(v_entries_609_, v_x2_606_);
v_indexes_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_603_, v___f_604_, v_indexes_610_, v_fst_607_, v_f_615_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v_indexes_617_);
lean_ctor_set(v___x_612_, 0, v_entries_616_);
v___x_619_ = v___x_612_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_entries_616_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_indexes_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_dec(v_fst_607_);
lean_dec_ref(v_x2_606_);
lean_dec_ref(v___f_604_);
lean_dec_ref(v___f_603_);
return v_x1_605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1___boxed(lean_object* v_name_622_, lean_object* v___f_623_, lean_object* v___f_624_, lean_object* v_x1_625_, lean_object* v_x2_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Http_Trailer_erase___lam__1(v_name_622_, v___f_623_, v___f_624_, v_x1_625_, v_x2_626_);
lean_dec_ref(v_name_622_);
return v_res_627_;
}
}
static lean_object* _init_l_Std_Http_Trailer_erase___closed__0(void){
_start:
{
lean_object* v___f_628_; lean_object* v___f_629_; lean_object* v___x_630_; 
v___f_628_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v___f_629_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___x_630_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v___f_629_, v___f_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase(lean_object* v_trailer_631_, lean_object* v_name_632_){
_start:
{
lean_object* v___f_633_; lean_object* v___f_634_; uint8_t v___x_635_; 
v___f_633_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_634_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_632_);
v___x_635_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v___f_633_, v___f_634_, v_name_632_, v_trailer_631_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_name_632_);
return v_trailer_631_;
}
else
{
lean_object* v_entries_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_entries_636_ = lean_ctor_get(v_trailer_631_, 0);
lean_inc_ref(v_entries_636_);
lean_dec_ref(v_trailer_631_);
v___x_637_ = lean_obj_once(&l_Std_Http_Trailer_erase___closed__0, &l_Std_Http_Trailer_erase___closed__0_once, _init_l_Std_Http_Trailer_erase___closed__0);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_array_get_size(v_entries_636_);
v___x_640_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_641_ = lean_nat_dec_lt(v___x_638_, v___x_639_);
if (v___x_641_ == 0)
{
lean_dec_ref(v_entries_636_);
lean_dec_ref(v_name_632_);
return v___x_637_;
}
else
{
lean_object* v___f_642_; size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___f_642_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_erase___lam__1___boxed), 5, 3);
lean_closure_set(v___f_642_, 0, v_name_632_);
lean_closure_set(v___f_642_, 1, v___f_633_);
lean_closure_set(v___f_642_, 2, v___f_634_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_639_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_640_, v___f_642_, v_entries_636_, v___x_643_, v___x_644_, v___x_637_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size(lean_object* v_trailer_646_){
_start:
{
lean_object* v_entries_647_; lean_object* v___x_648_; 
v_entries_647_ = lean_ctor_get(v_trailer_646_, 0);
v___x_648_ = lean_array_get_size(v_entries_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size___boxed(lean_object* v_trailer_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_Http_Trailer_size(v_trailer_649_);
lean_dec_ref(v_trailer_649_);
return v_res_650_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Trailer_isEmpty(lean_object* v_trailer_651_){
_start:
{
lean_object* v_entries_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_entries_652_ = lean_ctor_get(v_trailer_651_, 0);
v___x_653_ = lean_array_get_size(v_entries_652_);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_nat_dec_eq(v___x_653_, v___x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_isEmpty___boxed(lean_object* v_trailer_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_Http_Trailer_isEmpty(v_trailer_656_);
lean_dec_ref(v_trailer_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge(lean_object* v_t1_659_, lean_object* v_t2_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_Http_Headers_merge(v_t1_659_, v_t2_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge___boxed(lean_object* v_t1_662_, lean_object* v_t2_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Std_Http_Trailer_merge(v_t1_662_, v_t2_663_);
lean_dec_ref(v_t2_663_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toList(lean_object* v_trailer_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_Http_Headers_toList(v_trailer_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray(lean_object* v_trailer_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_Http_Headers_toArray(v_trailer_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray___boxed(lean_object* v_trailer_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_Http_Trailer_toArray(v_trailer_669_);
lean_dec_ref(v_trailer_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg(lean_object* v_trailer_671_, lean_object* v_init_672_, lean_object* v_f_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_Http_Headers_fold___redArg(v_trailer_671_, v_init_672_, v_f_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg___boxed(lean_object* v_trailer_675_, lean_object* v_init_676_, lean_object* v_f_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_Http_Trailer_fold___redArg(v_trailer_675_, v_init_676_, v_f_677_);
lean_dec_ref(v_trailer_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold(lean_object* v_00_u03b1_679_, lean_object* v_trailer_680_, lean_object* v_init_681_, lean_object* v_f_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_Http_Headers_fold___redArg(v_trailer_680_, v_init_681_, v_f_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___boxed(lean_object* v_00_u03b1_684_, lean_object* v_trailer_685_, lean_object* v_init_686_, lean_object* v_f_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_Http_Trailer_fold(v_00_u03b1_684_, v_trailer_685_, v_init_686_, v_f_687_);
lean_dec_ref(v_trailer_685_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0(lean_object* v___x_689_, lean_object* v___x_690_, lean_object* v___x_691_, lean_object* v_name_692_, lean_object* v___x_693_, uint32_t v___x_694_, lean_object* v___x_695_, lean_object* v_it_696_, lean_object* v_acc_697_, lean_object* v_hP_698_, lean_object* v_recur_699_){
_start:
{
lean_object* v_it_701_; lean_object* v_out_702_; uint32_t v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v_it_727_; lean_object* v_startInclusive_728_; lean_object* v_endExclusive_729_; 
if (lean_obj_tag(v_it_696_) == 0)
{
lean_object* v_currPos_736_; lean_object* v_searcher_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_759_; 
v_currPos_736_ = lean_ctor_get(v_it_696_, 0);
v_searcher_737_ = lean_ctor_get(v_it_696_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_it_696_);
if (v_isSharedCheck_759_ == 0)
{
v___x_739_ = v_it_696_;
v_isShared_740_ = v_isSharedCheck_759_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_searcher_737_);
lean_inc(v_currPos_736_);
lean_dec(v_it_696_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_759_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
uint8_t v_decide_741_; 
v_decide_741_ = lean_nat_dec_eq(v_searcher_737_, v___x_693_);
if (v_decide_741_ == 0)
{
uint32_t v___x_742_; uint8_t v___x_743_; 
lean_dec(v___x_693_);
v___x_742_ = lean_string_utf8_get_fast(v_name_692_, v_searcher_737_);
v___x_743_ = lean_uint32_dec_eq(v___x_742_, v___x_694_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_string_utf8_next_fast(v_name_692_, v_searcher_737_);
lean_dec(v_searcher_737_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_744_);
v___x_746_ = v___x_739_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_currPos_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = lean_apply_4(v_recur_699_, v___x_746_, v_acc_697_, lean_box(0), lean_box(0));
return v___x_747_;
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_slice_752_; lean_object* v_nextIt_754_; 
v___x_749_ = lean_string_utf8_next_fast(v_name_692_, v_searcher_737_);
v___x_750_ = lean_nat_sub(v___x_749_, v_searcher_737_);
v___x_751_ = lean_nat_add(v_searcher_737_, v___x_750_);
lean_dec(v___x_750_);
v_slice_752_ = l_String_Slice_subslice_x21(v___x_695_, v_currPos_736_, v_searcher_737_);
lean_inc(v___x_751_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_751_);
lean_ctor_set(v___x_739_, 0, v___x_751_);
v_nextIt_754_ = v___x_739_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_751_);
v_nextIt_754_ = v_reuseFailAlloc_757_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v_startInclusive_755_; lean_object* v_endExclusive_756_; 
v_startInclusive_755_ = lean_ctor_get(v_slice_752_, 0);
lean_inc(v_startInclusive_755_);
v_endExclusive_756_ = lean_ctor_get(v_slice_752_, 1);
lean_inc(v_endExclusive_756_);
lean_dec_ref(v_slice_752_);
v_it_727_ = v_nextIt_754_;
v_startInclusive_728_ = v_startInclusive_755_;
v_endExclusive_729_ = v_endExclusive_756_;
goto v___jp_726_;
}
}
}
else
{
lean_object* v___x_758_; 
lean_del_object(v___x_739_);
lean_dec(v_searcher_737_);
v___x_758_ = lean_box(1);
v_it_727_ = v___x_758_;
v_startInclusive_728_ = v_currPos_736_;
v_endExclusive_729_ = v___x_693_;
goto v___jp_726_;
}
}
}
else
{
lean_dec_ref(v_recur_699_);
lean_dec(v___x_693_);
return v_acc_697_;
}
v___jp_700_:
{
if (lean_obj_tag(v_acc_697_) == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v_out_702_);
v___x_704_ = lean_apply_4(v_recur_699_, v_it_701_, v___x_703_, lean_box(0), lean_box(0));
return v___x_704_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_716_; 
v_val_705_ = lean_ctor_get(v_acc_697_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_acc_697_);
if (v_isSharedCheck_716_ == 0)
{
v___x_707_ = v_acc_697_;
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v_acc_697_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_709_ = lean_string_utf8_extract_fast(v___x_689_, v___x_690_, v___x_691_);
v___x_710_ = lean_string_append(v_val_705_, v___x_709_);
lean_dec_ref(v___x_709_);
v___x_711_ = lean_string_append(v___x_710_, v_out_702_);
lean_dec_ref(v_out_702_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_711_);
v___x_713_ = v___x_707_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = lean_apply_4(v_recur_699_, v_it_701_, v___x_713_, lean_box(0), lean_box(0));
return v___x_714_;
}
}
}
}
v___jp_717_:
{
if (v___y_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_string_utf8_set(v___y_719_, v___x_690_, v___y_718_);
v_it_701_ = v___y_720_;
v_out_702_ = v___x_722_;
goto v___jp_700_;
}
else
{
uint32_t v___x_723_; uint32_t v___x_724_; lean_object* v___x_725_; 
v___x_723_ = 4294967264;
v___x_724_ = lean_uint32_add(v___y_718_, v___x_723_);
v___x_725_ = lean_string_utf8_set(v___y_719_, v___x_690_, v___x_724_);
v_it_701_ = v___y_720_;
v_out_702_ = v___x_725_;
goto v___jp_700_;
}
}
v___jp_726_:
{
lean_object* v___x_730_; uint32_t v___x_731_; uint32_t v___x_732_; uint8_t v___x_733_; 
v___x_730_ = lean_string_utf8_extract_fast(v_name_692_, v_startInclusive_728_, v_endExclusive_729_);
lean_dec(v_endExclusive_729_);
lean_dec(v_startInclusive_728_);
v___x_731_ = lean_string_utf8_get(v___x_730_, v___x_690_);
v___x_732_ = 97;
v___x_733_ = lean_uint32_dec_le(v___x_732_, v___x_731_);
if (v___x_733_ == 0)
{
v___y_718_ = v___x_731_;
v___y_719_ = v___x_730_;
v___y_720_ = v_it_727_;
v___y_721_ = v___x_733_;
goto v___jp_717_;
}
else
{
uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_734_ = 122;
v___x_735_ = lean_uint32_dec_le(v___x_731_, v___x_734_);
v___y_718_ = v___x_731_;
v___y_719_ = v___x_730_;
v___y_720_ = v_it_727_;
v___y_721_ = v___x_735_;
goto v___jp_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0___boxed(lean_object* v___x_760_, lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v_name_763_, lean_object* v___x_764_, lean_object* v___x_765_, lean_object* v___x_766_, lean_object* v_it_767_, lean_object* v_acc_768_, lean_object* v_hP_769_, lean_object* v_recur_770_){
_start:
{
uint32_t v___x_685__boxed_771_; lean_object* v_res_772_; 
v___x_685__boxed_771_ = lean_unbox_uint32(v___x_765_);
lean_dec(v___x_765_);
v_res_772_ = l_Std_Http_Trailer_instEncodeV11___lam__0(v___x_760_, v___x_761_, v___x_762_, v_name_763_, v___x_764_, v___x_685__boxed_771_, v___x_766_, v_it_767_, v_acc_768_, v_hP_769_, v_recur_770_);
lean_dec_ref(v___x_766_);
lean_dec_ref(v_name_763_);
lean_dec(v___x_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
return v_res_772_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2));
v___x_777_ = lean_string_utf8_byte_size(v___x_776_);
return v___x_777_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_778_; lean_object* v___x_779_; 
v___x_778_ = 45;
v___x_779_ = lean_box_uint32(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1(lean_object* v_buf_780_, lean_object* v_name_781_, lean_object* v_value_782_){
_start:
{
lean_object* v___y_784_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_it_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___f_803_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1));
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_string_utf8_byte_size(v_name_781_);
lean_inc_ref(v_name_781_);
v___x_806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_806_, 0, v_name_781_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
lean_ctor_set(v___x_806_, 2, v___x_805_);
lean_inc_ref(v___x_806_);
v_it_807_ = l_String_Slice_splitToSubslice___redArg(v___x_806_, v___f_803_);
v___x_808_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2));
v___x_809_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3, &l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__1___closed__3);
v___x_810_ = l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1;
v___f_811_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_811_, 0, v___x_808_);
lean_closure_set(v___f_811_, 1, v___x_804_);
lean_closure_set(v___f_811_, 2, v___x_809_);
lean_closure_set(v___f_811_, 3, v_name_781_);
lean_closure_set(v___f_811_, 4, v___x_805_);
lean_closure_set(v___f_811_, 5, v___x_810_);
lean_closure_set(v___f_811_, 6, v___x_806_);
v___x_812_ = lean_box(0);
v___x_813_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_811_, v_it_807_, v___x_812_, lean_box(0));
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v___x_814_; 
v___x_814_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___y_784_ = v___x_814_;
goto v___jp_783_;
}
else
{
lean_object* v_val_815_; 
v_val_815_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v___x_813_, 1);
v___y_784_ = v_val_815_;
goto v___jp_783_;
}
v___jp_783_:
{
lean_object* v_data_785_; lean_object* v_size_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_802_; 
v_data_785_ = lean_ctor_get(v_buf_780_, 0);
v_size_786_ = lean_ctor_get(v_buf_780_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_buf_780_);
if (v_isSharedCheck_802_ == 0)
{
v___x_788_ = v_buf_780_;
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_size_786_);
lean_inc(v_data_785_);
lean_dec(v_buf_780_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_790_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0));
v___x_791_ = lean_string_append(v___y_784_, v___x_790_);
v___x_792_ = lean_string_append(v___x_791_, v_value_782_);
v___x_793_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10));
v___x_794_ = lean_string_append(v___x_792_, v___x_793_);
v___x_795_ = lean_string_to_utf8(v___x_794_);
lean_dec_ref(v___x_794_);
lean_inc_ref(v___x_795_);
v___x_796_ = lean_array_push(v_data_785_, v___x_795_);
v___x_797_ = lean_byte_array_size(v___x_795_);
lean_dec_ref(v___x_795_);
v___x_798_ = lean_nat_add(v_size_786_, v___x_797_);
lean_dec(v_size_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_798_);
lean_ctor_set(v___x_788_, 0, v___x_796_);
v___x_800_ = v___x_788_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___boxed(lean_object* v_buf_816_, lean_object* v_name_817_, lean_object* v_value_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_Http_Trailer_instEncodeV11___lam__1(v_buf_816_, v_name_817_, v_value_818_);
lean_dec_ref(v_value_818_);
return v_res_819_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0));
v___x_822_ = lean_string_to_utf8(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1);
v___x_824_ = lean_byte_array_size(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_826_ = lean_byte_array_size(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2(lean_object* v___f_827_, lean_object* v_buffer_828_, lean_object* v_trailer_829_){
_start:
{
lean_object* v_data_830_; lean_object* v_size_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_856_; 
v_data_830_ = lean_ctor_get(v_buffer_828_, 0);
v_size_831_ = lean_ctor_get(v_buffer_828_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v_buffer_828_);
if (v_isSharedCheck_856_ == 0)
{
v___x_833_ = v_buffer_828_;
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_size_831_);
lean_inc(v_data_830_);
lean_dec(v_buffer_828_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_856_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_835_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1);
v___x_836_ = lean_array_push(v_data_830_, v___x_835_);
v___x_837_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2);
v___x_838_ = lean_nat_add(v_size_831_, v___x_837_);
lean_dec(v_size_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_838_);
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_840_ = v___x_833_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_855_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v_data_842_; lean_object* v_size_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_854_; 
v___x_841_ = l_Std_Http_Headers_fold___redArg(v_trailer_829_, v___x_840_, v___f_827_);
v_data_842_ = lean_ctor_get(v___x_841_, 0);
v_size_843_ = lean_ctor_get(v___x_841_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_854_ == 0)
{
v___x_845_ = v___x_841_;
v_isShared_846_ = v_isSharedCheck_854_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_size_843_);
lean_inc(v_data_842_);
lean_dec(v___x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_854_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_847_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_848_ = lean_array_push(v_data_842_, v___x_847_);
v___x_849_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3);
v___x_850_ = lean_nat_add(v_size_843_, v___x_849_);
lean_dec(v_size_843_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_850_);
lean_ctor_set(v___x_845_, 0, v___x_848_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___boxed(lean_object* v___f_857_, lean_object* v_buffer_858_, lean_object* v_trailer_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_Http_Trailer_instEncodeV11___lam__2(v___f_857_, v_buffer_858_, v_trailer_859_);
lean_dec_ref(v_trailer_859_);
return v_res_860_;
}
}
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Chunk(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers(builtin);
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
lean_object* runtime_initialize_Std_Http_Internal_String(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Chunk(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam = _init_l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam();
lean_mark_persistent(l_Std_Http_Chunk_ExtensionName_isValidExtensionName___autoParam);
l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam = _init_l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam();
lean_mark_persistent(l_Std_Http_Chunk_ExtensionValue_isValidExtensionValue___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers(uint8_t builtin);
lean_object* initialize_Std_Http_Internal_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Chunk(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Chunk(builtin);
}
#ifdef __cplusplus
}
#endif
