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
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
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
static const lean_closure_object l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2 = (const lean_object*)&l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2_value;
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
lean_object* v_head_272_; lean_object* v_tail_273_; uint32_t v___x_298_; uint32_t v___x_299_; uint8_t v___x_300_; 
v_head_272_ = lean_ctor_get(v_x_270_, 0);
v_tail_273_ = lean_ctor_get(v_x_270_, 1);
v___x_298_ = 9;
v___x_299_ = lean_unbox_uint32(v_head_272_);
v___x_300_ = lean_uint32_dec_eq(v___x_299_, v___x_298_);
if (v___x_300_ == 0)
{
uint32_t v___x_301_; uint32_t v___x_302_; uint8_t v___x_303_; 
v___x_301_ = 32;
v___x_302_ = lean_unbox_uint32(v_head_272_);
v___x_303_ = lean_uint32_dec_eq(v___x_302_, v___x_301_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_304_ = 33;
v___x_305_ = lean_unbox_uint32(v_head_272_);
v___x_306_ = lean_uint32_dec_eq(v___x_305_, v___x_304_);
if (v___x_306_ == 0)
{
uint32_t v___x_307_; uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_307_ = 35;
v___x_308_ = lean_unbox_uint32(v_head_272_);
v___x_309_ = lean_uint32_dec_le(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
goto v___jp_290_;
}
else
{
uint32_t v___x_310_; uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_310_ = 91;
v___x_311_ = lean_unbox_uint32(v_head_272_);
v___x_312_ = lean_uint32_dec_le(v___x_311_, v___x_310_);
if (v___x_312_ == 0)
{
goto v___jp_290_;
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
}
else
{
v_x_270_ = v_tail_273_;
goto _start;
}
v___jp_274_:
{
uint32_t v___x_275_; uint32_t v___x_276_; uint8_t v___x_277_; 
v___x_275_ = 9;
v___x_276_ = lean_unbox_uint32(v_head_272_);
v___x_277_ = lean_uint32_dec_eq(v___x_276_, v___x_275_);
if (v___x_277_ == 0)
{
uint32_t v___x_278_; uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_278_ = 32;
v___x_279_ = lean_unbox_uint32(v_head_272_);
v___x_280_ = lean_uint32_dec_eq(v___x_279_, v___x_278_);
if (v___x_280_ == 0)
{
uint32_t v___x_281_; uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_281_ = 33;
v___x_282_ = lean_unbox_uint32(v_head_272_);
v___x_283_ = lean_uint32_dec_le(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
return v___x_283_;
}
else
{
uint32_t v___x_284_; uint32_t v___x_285_; uint8_t v___x_286_; 
v___x_284_ = 126;
v___x_285_ = lean_unbox_uint32(v_head_272_);
v___x_286_ = lean_uint32_dec_le(v___x_285_, v___x_284_);
if (v___x_286_ == 0)
{
return v___x_286_;
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
}
v___jp_290_:
{
uint32_t v___x_291_; uint32_t v___x_292_; uint8_t v___x_293_; 
v___x_291_ = 93;
v___x_292_ = lean_unbox_uint32(v_head_272_);
v___x_293_ = lean_uint32_dec_le(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
goto v___jp_274_;
}
else
{
uint32_t v___x_294_; uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_294_ = 126;
v___x_295_ = lean_unbox_uint32(v_head_272_);
v___x_296_ = lean_uint32_dec_le(v___x_295_, v___x_294_);
if (v___x_296_ == 0)
{
goto v___jp_274_;
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
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0___boxed(lean_object* v_x_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(v_x_317_);
lean_dec(v_x_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x3f(lean_object* v_s_320_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
lean_inc_ref(v_s_320_);
v___x_321_ = lean_string_data(v_s_320_);
v___x_322_ = l_List_all___at___00Std_Http_Chunk_ExtensionValue_ofString_x3f_spec__0(v___x_321_);
lean_dec(v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v_s_320_);
v___x_323_ = lean_box(0);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_s_320_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(lean_object* v_msg_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___x_327_ = lean_panic_fn_borrowed(v___x_326_, v_msg_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ExtensionValue_ofString_x21(lean_object* v_s_330_){
_start:
{
lean_object* v___x_331_; 
lean_inc_ref(v_s_330_);
v___x_331_ = l_Std_Http_Chunk_ExtensionValue_ofString_x3f(v_s_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_332_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionName_ofString_x21___closed__0));
v___x_333_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__0));
v___x_334_ = lean_unsigned_to_nat(152u);
v___x_335_ = lean_unsigned_to_nat(12u);
v___x_336_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_ofString_x21___closed__1));
v___x_337_ = l_String_quote(v_s_330_);
v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
lean_dec_ref(v___x_337_);
v___x_339_ = l_mkPanicMessageWithDecl(v___x_332_, v___x_333_, v___x_334_, v___x_335_, v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_panic___at___00Std_Http_Chunk_ExtensionValue_ofString_x21_spec__0(v___x_339_);
return v___x_340_;
}
else
{
lean_object* v_val_341_; 
lean_dec_ref(v_s_330_);
v_val_341_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_341_);
lean_dec_ref_known(v___x_331_, 1);
return v_val_341_;
}
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk_default___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = ((lean_object*)(l_Std_Http_instInhabitedChunk_default___closed__0));
v___x_345_ = l_ByteArray_empty;
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk_default(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Std_Http_instInhabitedChunk_default___closed__1, &l_Std_Http_instInhabitedChunk_default___closed__1_once, _init_l_Std_Http_instInhabitedChunk_default___closed__1);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedChunk(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Std_Http_instInhabitedChunk_default;
return v___x_348_;
}
}
static lean_object* _init_l_Std_Http_Chunk_empty(void){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Std_Http_instInhabitedChunk_default___closed__1, &l_Std_Http_instInhabitedChunk_default___closed__1_once, _init_l_Std_Http_instInhabitedChunk_default___closed__1);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_ofByteArray(lean_object* v_data_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Std_Http_instInhabitedChunk_default___closed__0));
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_data_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_insertExtension(lean_object* v_chunk_353_, lean_object* v_key_354_, lean_object* v_value_355_){
_start:
{
lean_object* v_data_356_; lean_object* v_extensions_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_367_; 
v_data_356_ = lean_ctor_get(v_chunk_353_, 0);
v_extensions_357_ = lean_ctor_get(v_chunk_353_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v_chunk_353_);
if (v_isSharedCheck_367_ == 0)
{
v___x_359_ = v_chunk_353_;
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_extensions_357_);
lean_inc(v_data_356_);
lean_dec(v_chunk_353_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_367_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_value_355_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_key_354_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_array_push(v_extensions_357_, v___x_362_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_363_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_data_356_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_toString_x3f(lean_object* v_chunk_368_){
_start:
{
lean_object* v_data_369_; uint8_t v___x_370_; 
v_data_369_ = lean_ctor_get(v_chunk_368_, 0);
lean_inc_ref(v_data_369_);
lean_dec_ref(v_chunk_368_);
v___x_370_ = lean_string_validate_utf8(v_data_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec_ref(v_data_369_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_string_from_utf8_unchecked(v_data_369_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0(lean_object* v_x1_374_, lean_object* v_x2_375_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_byte_array_size(v_x2_375_);
v___x_377_ = lean_nat_add(v_x1_374_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__0___boxed(lean_object* v_x1_378_, lean_object* v_x2_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Http_Chunk_instEncodeV11___lam__0(v_x1_378_, v_x2_379_);
lean_dec_ref(v_x2_379_);
lean_dec(v_x1_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__1(lean_object* v_x1_383_, lean_object* v_x2_384_){
_start:
{
lean_object* v_fst_385_; lean_object* v_snd_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_fst_385_ = lean_ctor_get(v_x2_384_, 0);
lean_inc(v_fst_385_);
v_snd_386_ = lean_ctor_get(v_x2_384_, 1);
lean_inc(v_snd_386_);
lean_dec_ref(v_x2_384_);
v___x_387_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__0));
v___x_388_ = lean_string_append(v_x1_383_, v___x_387_);
v___x_389_ = lean_string_append(v___x_388_, v_fst_385_);
lean_dec(v_fst_385_);
if (lean_obj_tag(v_snd_386_) == 0)
{
return v___x_389_;
}
else
{
lean_object* v_val_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_val_390_ = lean_ctor_get(v_snd_386_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v_snd_386_, 1);
v___x_391_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__1___closed__1));
v___x_392_ = l_Std_Http_Internal_quoteHttpString___redArg(v_val_390_);
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
lean_dec_ref(v___x_392_);
v___x_394_ = lean_string_append(v___x_389_, v___x_393_);
lean_dec_ref(v___x_393_);
return v___x_394_;
}
}
}
static lean_object* _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10));
v___x_416_ = lean_string_to_utf8(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Chunk_instEncodeV11___lam__2(lean_object* v___f_417_, lean_object* v___f_418_, lean_object* v___f_419_, lean_object* v_buffer_420_, lean_object* v_chunk_421_){
_start:
{
lean_object* v___y_423_; lean_object* v_data_437_; lean_object* v_extensions_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_485_; 
v_data_437_ = lean_ctor_get(v_chunk_421_, 0);
v_extensions_438_ = lean_ctor_get(v_chunk_421_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_chunk_421_);
if (v_isSharedCheck_485_ == 0)
{
v___x_440_ = v_chunk_421_;
v_isShared_441_ = v_isSharedCheck_485_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_extensions_438_);
lean_inc(v_data_437_);
lean_dec(v_chunk_421_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_485_;
goto v_resetjp_439_;
}
v___jp_422_:
{
lean_object* v_data_424_; lean_object* v_size_425_; lean_object* v_data_426_; lean_object* v_size_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
v_data_424_ = lean_ctor_get(v_buffer_420_, 0);
lean_inc_ref(v_data_424_);
v_size_425_ = lean_ctor_get(v_buffer_420_, 1);
lean_inc(v_size_425_);
lean_dec_ref(v_buffer_420_);
v_data_426_ = lean_ctor_get(v___y_423_, 0);
v_size_427_ = lean_ctor_get(v___y_423_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___y_423_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v___y_423_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_size_427_);
lean_inc(v_data_426_);
lean_dec(v___y_423_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = l_Array_append___redArg(v_data_424_, v_data_426_);
lean_dec_ref(v_data_426_);
v___x_432_ = lean_nat_add(v_size_425_, v_size_427_);
lean_dec(v_size_427_);
lean_dec(v_size_425_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 1, v___x_432_);
lean_ctor_set(v___x_429_, 0, v___x_431_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
v_resetjp_439_:
{
lean_object* v_chunkLen_442_; lean_object* v___y_444_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_chunkLen_442_ = lean_byte_array_size(v_data_437_);
v___x_473_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_extensions_438_);
v___x_476_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_477_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_extensions_438_);
lean_dec_ref(v___f_419_);
v___y_444_ = v___x_473_;
goto v___jp_443_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_le(v___x_475_, v___x_475_);
if (v___x_478_ == 0)
{
if (v___x_477_ == 0)
{
lean_dec_ref(v_extensions_438_);
lean_dec_ref(v___f_419_);
v___y_444_ = v___x_473_;
goto v___jp_443_;
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___x_475_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_476_, v___f_419_, v_extensions_438_, v___x_479_, v___x_480_, v___x_473_);
v___y_444_ = v___x_481_;
goto v___jp_443_;
}
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_475_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_476_, v___f_419_, v_extensions_438_, v___x_482_, v___x_483_, v___x_473_);
v___y_444_ = v___x_484_;
goto v___jp_443_;
}
}
v___jp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; size_t v_sz_449_; size_t v___x_450_; lean_object* v___x_451_; lean_object* v_size_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_445_ = lean_unsigned_to_nat(16u);
v___x_446_ = l_Nat_toDigits(v___x_445_, v_chunkLen_442_);
v___x_447_ = lean_array_mk(v___x_446_);
v___x_448_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v_sz_449_ = lean_array_size(v___x_447_);
v___x_450_ = ((size_t)0ULL);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_448_, v___f_417_, v_sz_449_, v___x_450_, v___x_447_);
v_size_452_ = lean_byte_array_mk(v___x_451_);
v___x_453_ = lean_string_to_utf8(v___y_444_);
lean_dec_ref(v___y_444_);
v___x_454_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_455_ = lean_unsigned_to_nat(5u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_array_push(v___x_456_, v_size_452_);
v___x_458_ = lean_array_push(v___x_457_, v___x_453_);
v___x_459_ = lean_array_push(v___x_458_, v___x_454_);
v___x_460_ = lean_array_push(v___x_459_, v_data_437_);
v___x_461_ = lean_array_push(v___x_460_, v___x_454_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_array_get_size(v___x_461_);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_466_; 
lean_dec_ref(v___f_418_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_462_);
lean_ctor_set(v___x_440_, 0, v___x_461_);
v___x_466_ = v___x_440_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_462_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
v___y_423_ = v___x_466_;
goto v___jp_422_;
}
}
else
{
size_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_usize_of_nat(v___x_463_);
lean_inc_ref(v___x_461_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_448_, v___f_418_, v___x_461_, v___x_450_, v___x_468_, v___x_462_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_469_);
lean_ctor_set(v___x_440_, 0, v___x_461_);
v___x_471_ = v___x_440_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
v___y_423_ = v___x_471_;
goto v___jp_422_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Http_instInhabitedTrailer_default(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_494_;
}
}
static lean_object* _init_l_Std_Http_instInhabitedTrailer(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_Http_instInhabitedHeaders_default;
return v___x_495_;
}
}
static lean_object* _init_l_Std_Http_Trailer_empty(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_Http_Headers_empty;
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert___lam__0(lean_object* v_i_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_mk_empty_array_with_capacity(v___x_499_);
v___x_501_ = lean_array_push(v___x_500_, v_i_497_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_511_; 
v_val_503_ = lean_ctor_get(v_x_498_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v_x_498_);
if (v_isSharedCheck_511_ == 0)
{
v___x_505_ = v_x_498_;
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v_x_498_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_511_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_array_push(v_val_503_, v_i_497_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_507_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert(lean_object* v_trailer_513_, lean_object* v_name_514_, lean_object* v_value_515_){
_start:
{
lean_object* v_entries_516_; lean_object* v_indexes_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_531_; 
v_entries_516_ = lean_ctor_get(v_trailer_513_, 0);
v_indexes_517_ = lean_ctor_get(v_trailer_513_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_trailer_513_);
if (v_isSharedCheck_531_ == 0)
{
v___x_519_ = v_trailer_513_;
v_isShared_520_ = v_isSharedCheck_531_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_indexes_517_);
lean_inc(v_entries_516_);
lean_dec(v_trailer_513_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_531_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v_i_523_; lean_object* v_f_524_; lean_object* v___x_525_; lean_object* v_entries_526_; lean_object* v_indexes_527_; lean_object* v___x_529_; 
v___f_521_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_522_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v_i_523_ = lean_array_get_size(v_entries_516_);
v_f_524_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_524_, 0, v_i_523_);
lean_inc_ref(v_name_514_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_name_514_);
lean_ctor_set(v___x_525_, 1, v_value_515_);
v_entries_526_ = lean_array_push(v_entries_516_, v___x_525_);
v_indexes_527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_521_, v___f_522_, v_indexes_517_, v_name_514_, v_f_524_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v_indexes_527_);
lean_ctor_set(v___x_519_, 0, v_entries_526_);
v___x_529_ = v___x_519_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_entries_526_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_indexes_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_insert_x21(lean_object* v_trailer_532_, lean_object* v_name_533_, lean_object* v_value_534_){
_start:
{
lean_object* v_entries_535_; lean_object* v_indexes_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_552_; 
v_entries_535_ = lean_ctor_get(v_trailer_532_, 0);
v_indexes_536_ = lean_ctor_get(v_trailer_532_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_trailer_532_);
if (v_isSharedCheck_552_ == 0)
{
v___x_538_ = v_trailer_532_;
v_isShared_539_ = v_isSharedCheck_552_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_indexes_536_);
lean_inc(v_entries_535_);
lean_dec(v_trailer_532_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_552_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___f_542_; lean_object* v___f_543_; lean_object* v_i_544_; lean_object* v_f_545_; lean_object* v___x_546_; lean_object* v_entries_547_; lean_object* v_indexes_548_; lean_object* v___x_550_; 
v___x_540_ = l_Std_Http_Header_Name_ofString_x21(v_name_533_);
v___x_541_ = l_Std_Http_Header_Value_ofString_x21(v_value_534_);
v___f_542_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_543_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v_i_544_ = lean_array_get_size(v_entries_535_);
v_f_545_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_545_, 0, v_i_544_);
lean_inc_ref(v___x_540_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_540_);
lean_ctor_set(v___x_546_, 1, v___x_541_);
v_entries_547_ = lean_array_push(v_entries_535_, v___x_546_);
v_indexes_548_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_542_, v___f_543_, v_indexes_536_, v___x_540_, v_f_545_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_indexes_548_);
lean_ctor_set(v___x_538_, 0, v_entries_547_);
v___x_550_ = v___x_538_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_entries_547_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_indexes_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f(lean_object* v_trailer_553_, lean_object* v_name_554_){
_start:
{
lean_object* v_entries_555_; lean_object* v_indexes_556_; lean_object* v___f_557_; lean_object* v___f_558_; uint8_t v___x_559_; 
v_entries_555_ = lean_ctor_get(v_trailer_553_, 0);
v_indexes_556_ = lean_ctor_get(v_trailer_553_, 1);
v___f_557_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_558_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_554_);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_557_, v___f_558_, v_indexes_556_, v_name_554_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec_ref(v_name_554_);
v___x_560_ = lean_box(0);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_entry_563_; lean_object* v___x_564_; lean_object* v_snd_565_; lean_object* v___x_566_; 
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_557_, v___f_558_, v_indexes_556_, v_name_554_);
v___x_562_ = lean_unsigned_to_nat(0u);
v_entry_563_ = lean_array_fget(v___x_561_, v___x_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_array_fget_borrowed(v_entries_555_, v_entry_563_);
lean_dec(v_entry_563_);
v_snd_565_ = lean_ctor_get(v___x_564_, 1);
lean_inc(v_snd_565_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_snd_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_get_x3f___boxed(lean_object* v_trailer_567_, lean_object* v_name_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Trailer_get_x3f(v_trailer_567_, v_name_568_);
lean_dec_ref(v_trailer_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0(lean_object* v___x_570_, lean_object* v_entries_571_, lean_object* v_x1_572_, lean_object* v_x2_573_, lean_object* v_x3_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_snd_577_; 
v___x_575_ = lean_array_fget_borrowed(v___x_570_, v_x1_572_);
v___x_576_ = lean_array_fget_borrowed(v_entries_571_, v___x_575_);
v_snd_577_ = lean_ctor_get(v___x_576_, 1);
lean_inc(v_snd_577_);
return v_snd_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f___lam__0___boxed(lean_object* v___x_578_, lean_object* v_entries_579_, lean_object* v_x1_580_, lean_object* v_x2_581_, lean_object* v_x3_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Http_Trailer_getAll_x3f___lam__0(v___x_578_, v_entries_579_, v_x1_580_, v_x2_581_, v_x3_582_);
lean_dec(v_x2_581_);
lean_dec(v_x1_580_);
lean_dec_ref(v_entries_579_);
lean_dec(v___x_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_getAll_x3f(lean_object* v_trailer_584_, lean_object* v_name_585_){
_start:
{
lean_object* v_entries_586_; lean_object* v_indexes_587_; lean_object* v___f_588_; lean_object* v___f_589_; uint8_t v___x_590_; 
v_entries_586_ = lean_ctor_get(v_trailer_584_, 0);
lean_inc_ref(v_entries_586_);
v_indexes_587_ = lean_ctor_get(v_trailer_584_, 1);
lean_inc_ref(v_indexes_587_);
lean_dec_ref(v_trailer_584_);
v___f_588_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_589_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
lean_inc_ref(v_name_585_);
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_588_, v___f_589_, v_indexes_587_, v_name_585_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_indexes_587_);
lean_dec_ref(v_entries_586_);
lean_dec_ref(v_name_585_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___x_594_; size_t v_sz_595_; size_t v___x_596_; lean_object* v_entries_597_; lean_object* v___x_598_; 
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v___f_588_, v___f_589_, v_indexes_587_, v_name_585_);
lean_dec_ref(v_indexes_587_);
lean_inc_n(v___x_592_, 2);
v___f_593_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_getAll_x3f___lam__0___boxed), 5, 2);
lean_closure_set(v___f_593_, 0, v___x_592_);
lean_closure_set(v___f_593_, 1, v_entries_586_);
v___x_594_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v_sz_595_ = lean_array_size(v___x_592_);
v___x_596_ = ((size_t)0ULL);
v_entries_597_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_594_, v___x_592_, v___f_593_, v_sz_595_, v___x_596_, v___x_592_);
lean_dec(v___x_592_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_entries_597_);
return v___x_598_;
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Trailer_contains(lean_object* v_trailer_599_, lean_object* v_name_600_){
_start:
{
lean_object* v_indexes_601_; lean_object* v___f_602_; lean_object* v___f_603_; uint8_t v___x_604_; 
v_indexes_601_ = lean_ctor_get(v_trailer_599_, 1);
v___f_602_ = ((lean_object*)(l_Std_Http_Trailer_insert___closed__0));
v___f_603_ = ((lean_object*)(l_Std_Http_Chunk_instHashableExtensionName___closed__0));
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_602_, v___f_603_, v_indexes_601_, v_name_600_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_contains___boxed(lean_object* v_trailer_605_, lean_object* v_name_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Std_Http_Trailer_contains(v_trailer_605_, v_name_606_);
lean_dec_ref(v_trailer_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1(lean_object* v_name_609_, lean_object* v___f_610_, lean_object* v___f_611_, lean_object* v_x1_612_, lean_object* v_x2_613_){
_start:
{
lean_object* v_fst_614_; uint8_t v___x_615_; 
v_fst_614_ = lean_ctor_get(v_x2_613_, 0);
lean_inc(v_fst_614_);
v___x_615_ = lean_string_dec_eq(v_name_609_, v_fst_614_);
if (v___x_615_ == 0)
{
lean_object* v_entries_616_; lean_object* v_indexes_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_628_; 
v_entries_616_ = lean_ctor_get(v_x1_612_, 0);
v_indexes_617_ = lean_ctor_get(v_x1_612_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x1_612_);
if (v_isSharedCheck_628_ == 0)
{
v___x_619_ = v_x1_612_;
v_isShared_620_ = v_isSharedCheck_628_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_indexes_617_);
lean_inc(v_entries_616_);
lean_dec(v_x1_612_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_628_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_i_621_; lean_object* v_f_622_; lean_object* v_entries_623_; lean_object* v_indexes_624_; lean_object* v___x_626_; 
v_i_621_ = lean_array_get_size(v_entries_616_);
v_f_622_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_insert___lam__0), 2, 1);
lean_closure_set(v_f_622_, 0, v_i_621_);
v_entries_623_ = lean_array_push(v_entries_616_, v_x2_613_);
v_indexes_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_610_, v___f_611_, v_indexes_617_, v_fst_614_, v_f_622_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_indexes_624_);
lean_ctor_set(v___x_619_, 0, v_entries_623_);
v___x_626_ = v___x_619_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_entries_623_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_indexes_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_dec(v_fst_614_);
lean_dec_ref(v_x2_613_);
lean_dec_ref(v___f_611_);
lean_dec_ref(v___f_610_);
return v_x1_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_erase___lam__1___boxed(lean_object* v_name_629_, lean_object* v___f_630_, lean_object* v___f_631_, lean_object* v_x1_632_, lean_object* v_x2_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Std_Http_Trailer_erase___lam__1(v_name_629_, v___f_630_, v___f_631_, v_x1_632_, v_x2_633_);
lean_dec_ref(v_name_629_);
return v_res_634_;
}
}
static lean_object* _init_l_Std_Http_Trailer_erase___closed__0(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_635_;
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
lean_object* v_entries_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_entries_641_ = lean_ctor_get(v_trailer_636_, 0);
lean_inc_ref(v_entries_641_);
lean_dec_ref(v_trailer_636_);
v___x_642_ = lean_obj_once(&l_Std_Http_Trailer_erase___closed__0, &l_Std_Http_Trailer_erase___closed__0_once, _init_l_Std_Http_Trailer_erase___closed__0);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_array_get_size(v_entries_641_);
v___x_645_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__9));
v___x_646_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
if (v___x_646_ == 0)
{
lean_dec_ref(v_entries_641_);
lean_dec_ref(v_name_637_);
return v___x_642_;
}
else
{
lean_object* v___f_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v___f_647_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_erase___lam__1___boxed), 5, 3);
lean_closure_set(v___f_647_, 0, v_name_637_);
lean_closure_set(v___f_647_, 1, v___f_638_);
lean_closure_set(v___f_647_, 2, v___f_639_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = lean_usize_of_nat(v___x_644_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_645_, v___f_647_, v_entries_641_, v___x_648_, v___x_649_, v___x_642_);
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size(lean_object* v_trailer_651_){
_start:
{
lean_object* v_entries_652_; lean_object* v___x_653_; 
v_entries_652_ = lean_ctor_get(v_trailer_651_, 0);
v___x_653_ = lean_array_get_size(v_entries_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_size___boxed(lean_object* v_trailer_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_Http_Trailer_size(v_trailer_654_);
lean_dec_ref(v_trailer_654_);
return v_res_655_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Trailer_isEmpty(lean_object* v_trailer_656_){
_start:
{
lean_object* v_entries_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_entries_657_ = lean_ctor_get(v_trailer_656_, 0);
v___x_658_ = lean_array_get_size(v_entries_657_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_nat_dec_eq(v___x_658_, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_isEmpty___boxed(lean_object* v_trailer_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_Std_Http_Trailer_isEmpty(v_trailer_661_);
lean_dec_ref(v_trailer_661_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge(lean_object* v_t1_664_, lean_object* v_t2_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Std_Http_Headers_merge(v_t1_664_, v_t2_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_merge___boxed(lean_object* v_t1_667_, lean_object* v_t2_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Http_Trailer_merge(v_t1_667_, v_t2_668_);
lean_dec_ref(v_t2_668_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toList(lean_object* v_trailer_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Std_Http_Headers_toList(v_trailer_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray(lean_object* v_trailer_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Std_Http_Headers_toArray(v_trailer_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_toArray___boxed(lean_object* v_trailer_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Http_Trailer_toArray(v_trailer_674_);
lean_dec_ref(v_trailer_674_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg(lean_object* v_trailer_676_, lean_object* v_init_677_, lean_object* v_f_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_Http_Headers_fold___redArg(v_trailer_676_, v_init_677_, v_f_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___redArg___boxed(lean_object* v_trailer_680_, lean_object* v_init_681_, lean_object* v_f_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_Http_Trailer_fold___redArg(v_trailer_680_, v_init_681_, v_f_682_);
lean_dec_ref(v_trailer_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold(lean_object* v_00_u03b1_684_, lean_object* v_trailer_685_, lean_object* v_init_686_, lean_object* v_f_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_Http_Headers_fold___redArg(v_trailer_685_, v_init_686_, v_f_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_fold___boxed(lean_object* v_00_u03b1_689_, lean_object* v_trailer_690_, lean_object* v_init_691_, lean_object* v_f_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Http_Trailer_fold(v_00_u03b1_689_, v_trailer_690_, v_init_691_, v_f_692_);
lean_dec_ref(v_trailer_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0(lean_object* v___x_694_, lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v_name_697_, lean_object* v___x_698_, uint32_t v___x_699_, lean_object* v___x_700_, lean_object* v_it_701_, lean_object* v_acc_702_, lean_object* v_hP_703_, lean_object* v_recur_704_){
_start:
{
lean_object* v_it_706_; lean_object* v_out_707_; lean_object* v_it_723_; lean_object* v_startInclusive_724_; lean_object* v_endExclusive_725_; 
if (lean_obj_tag(v_it_701_) == 0)
{
lean_object* v_currPos_737_; lean_object* v_searcher_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_760_; 
v_currPos_737_ = lean_ctor_get(v_it_701_, 0);
v_searcher_738_ = lean_ctor_get(v_it_701_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_it_701_);
if (v_isSharedCheck_760_ == 0)
{
v___x_740_ = v_it_701_;
v_isShared_741_ = v_isSharedCheck_760_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_searcher_738_);
lean_inc(v_currPos_737_);
lean_dec(v_it_701_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_760_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v_decide_742_; 
v_decide_742_ = lean_nat_dec_eq(v_searcher_738_, v___x_698_);
if (v_decide_742_ == 0)
{
uint32_t v___x_743_; uint8_t v___x_744_; 
lean_dec(v___x_698_);
v___x_743_ = lean_string_utf8_get_fast(v_name_697_, v_searcher_738_);
v___x_744_ = lean_uint32_dec_eq(v___x_743_, v___x_699_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_string_utf8_next_fast(v_name_697_, v_searcher_738_);
lean_dec(v_searcher_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_745_);
v___x_747_ = v___x_740_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_currPos_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_745_);
v___x_747_ = v_reuseFailAlloc_749_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; 
v___x_748_ = lean_apply_4(v_recur_704_, v___x_747_, v_acc_702_, lean_box(0), lean_box(0));
return v___x_748_;
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_slice_753_; lean_object* v_nextIt_755_; 
v___x_750_ = lean_string_utf8_next_fast(v_name_697_, v_searcher_738_);
v___x_751_ = lean_nat_sub(v___x_750_, v_searcher_738_);
v___x_752_ = lean_nat_add(v_searcher_738_, v___x_751_);
lean_dec(v___x_751_);
v_slice_753_ = l_String_Slice_subslice_x21(v___x_700_, v_currPos_737_, v_searcher_738_);
lean_inc(v___x_752_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v___x_752_);
lean_ctor_set(v___x_740_, 0, v___x_752_);
v_nextIt_755_ = v___x_740_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_752_);
v_nextIt_755_ = v_reuseFailAlloc_758_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v_startInclusive_756_; lean_object* v_endExclusive_757_; 
v_startInclusive_756_ = lean_ctor_get(v_slice_753_, 0);
lean_inc(v_startInclusive_756_);
v_endExclusive_757_ = lean_ctor_get(v_slice_753_, 1);
lean_inc(v_endExclusive_757_);
lean_dec_ref(v_slice_753_);
v_it_723_ = v_nextIt_755_;
v_startInclusive_724_ = v_startInclusive_756_;
v_endExclusive_725_ = v_endExclusive_757_;
goto v___jp_722_;
}
}
}
else
{
lean_object* v___x_759_; 
lean_del_object(v___x_740_);
lean_dec(v_searcher_738_);
v___x_759_ = lean_box(1);
v_it_723_ = v___x_759_;
v_startInclusive_724_ = v_currPos_737_;
v_endExclusive_725_ = v___x_698_;
goto v___jp_722_;
}
}
}
else
{
lean_dec_ref(v_recur_704_);
lean_dec(v___x_698_);
return v_acc_702_;
}
v___jp_705_:
{
if (lean_obj_tag(v_acc_702_) == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_out_707_);
v___x_709_ = lean_apply_4(v_recur_704_, v_it_706_, v___x_708_, lean_box(0), lean_box(0));
return v___x_709_;
}
else
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_721_; 
v_val_710_ = lean_ctor_get(v_acc_702_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_acc_702_);
if (v_isSharedCheck_721_ == 0)
{
v___x_712_ = v_acc_702_;
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v_acc_702_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_714_ = lean_string_utf8_extract_fast(v___x_694_, v___x_695_, v___x_696_);
v___x_715_ = lean_string_append(v_val_710_, v___x_714_);
lean_dec_ref(v___x_714_);
v___x_716_ = lean_string_append(v___x_715_, v_out_707_);
lean_dec_ref(v_out_707_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_716_);
v___x_718_ = v___x_712_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_720_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; 
v___x_719_ = lean_apply_4(v_recur_704_, v_it_706_, v___x_718_, lean_box(0), lean_box(0));
return v___x_719_;
}
}
}
}
v___jp_722_:
{
lean_object* v___x_726_; uint32_t v___x_727_; uint32_t v___x_728_; uint8_t v___x_729_; 
v___x_726_ = lean_string_utf8_extract_fast(v_name_697_, v_startInclusive_724_, v_endExclusive_725_);
lean_dec(v_endExclusive_725_);
lean_dec(v_startInclusive_724_);
v___x_727_ = lean_string_utf8_get(v___x_726_, v___x_695_);
v___x_728_ = 97;
v___x_729_ = lean_uint32_dec_le(v___x_728_, v___x_727_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
v___x_730_ = lean_string_utf8_set(v___x_726_, v___x_695_, v___x_727_);
v_it_706_ = v_it_723_;
v_out_707_ = v___x_730_;
goto v___jp_705_;
}
else
{
uint32_t v___x_731_; uint8_t v___x_732_; 
v___x_731_ = 122;
v___x_732_ = lean_uint32_dec_le(v___x_727_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_string_utf8_set(v___x_726_, v___x_695_, v___x_727_);
v_it_706_ = v_it_723_;
v_out_707_ = v___x_733_;
goto v___jp_705_;
}
else
{
uint32_t v___x_734_; uint32_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = 4294967264;
v___x_735_ = lean_uint32_add(v___x_727_, v___x_734_);
v___x_736_ = lean_string_utf8_set(v___x_726_, v___x_695_, v___x_735_);
v_it_706_ = v_it_723_;
v_out_707_ = v___x_736_;
goto v___jp_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__0___boxed(lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v___x_763_, lean_object* v_name_764_, lean_object* v___x_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v_it_768_, lean_object* v_acc_769_, lean_object* v_hP_770_, lean_object* v_recur_771_){
_start:
{
uint32_t v___x_657__boxed_772_; lean_object* v_res_773_; 
v___x_657__boxed_772_ = lean_unbox_uint32(v___x_766_);
lean_dec(v___x_766_);
v_res_773_ = l_Std_Http_Trailer_instEncodeV11___lam__0(v___x_761_, v___x_762_, v___x_763_, v_name_764_, v___x_765_, v___x_657__boxed_772_, v___x_767_, v_it_768_, v_acc_769_, v_hP_770_, v_recur_771_);
lean_dec_ref(v___x_767_);
lean_dec_ref(v_name_764_);
lean_dec(v___x_763_);
lean_dec(v___x_762_);
lean_dec_ref(v___x_761_);
return v_res_773_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_777_; lean_object* v___x_778_; 
v___x_777_ = 45;
v___x_778_ = lean_box_uint32(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1(lean_object* v_buf_779_, lean_object* v_name_780_, lean_object* v_value_781_){
_start:
{
lean_object* v___y_783_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v_it_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___f_802_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__1));
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_string_utf8_byte_size(v_name_780_);
lean_inc_ref(v_name_780_);
v___x_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_805_, 0, v_name_780_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
lean_inc_ref(v___x_805_);
v_it_806_ = l_String_Slice_splitToSubslice___redArg(v___x_805_, v___f_802_);
v___x_807_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__2));
v___x_808_ = lean_unsigned_to_nat(1u);
v___x_809_ = l_Std_Http_Trailer_instEncodeV11___lam__1___boxed__const__1;
v___f_810_ = lean_alloc_closure((void*)(l_Std_Http_Trailer_instEncodeV11___lam__0___boxed), 11, 7);
lean_closure_set(v___f_810_, 0, v___x_807_);
lean_closure_set(v___f_810_, 1, v___x_803_);
lean_closure_set(v___f_810_, 2, v___x_808_);
lean_closure_set(v___f_810_, 3, v_name_780_);
lean_closure_set(v___f_810_, 4, v___x_804_);
lean_closure_set(v___f_810_, 5, v___x_809_);
lean_closure_set(v___f_810_, 6, v___x_805_);
v___x_811_ = lean_box(0);
v___x_812_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_810_, v_it_806_, v___x_811_, lean_box(0));
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; 
v___x_813_ = ((lean_object*)(l_Std_Http_Chunk_ExtensionValue_instInhabited___closed__0));
v___y_783_ = v___x_813_;
goto v___jp_782_;
}
else
{
lean_object* v_val_814_; 
v_val_814_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v___x_812_, 1);
v___y_783_ = v_val_814_;
goto v___jp_782_;
}
v___jp_782_:
{
lean_object* v_data_784_; lean_object* v_size_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_801_; 
v_data_784_ = lean_ctor_get(v_buf_779_, 0);
v_size_785_ = lean_ctor_get(v_buf_779_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_buf_779_);
if (v_isSharedCheck_801_ == 0)
{
v___x_787_ = v_buf_779_;
v_isShared_788_ = v_isSharedCheck_801_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_size_785_);
lean_inc(v_data_784_);
lean_dec(v_buf_779_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_801_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_789_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__1___closed__0));
v___x_790_ = lean_string_append(v___y_783_, v___x_789_);
v___x_791_ = lean_string_append(v___x_790_, v_value_781_);
v___x_792_ = ((lean_object*)(l_Std_Http_Chunk_instEncodeV11___lam__2___closed__10));
v___x_793_ = lean_string_append(v___x_791_, v___x_792_);
v___x_794_ = lean_string_to_utf8(v___x_793_);
lean_dec_ref(v___x_793_);
lean_inc_ref(v___x_794_);
v___x_795_ = lean_array_push(v_data_784_, v___x_794_);
v___x_796_ = lean_byte_array_size(v___x_794_);
lean_dec_ref(v___x_794_);
v___x_797_ = lean_nat_add(v_size_785_, v___x_796_);
lean_dec(v_size_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v___x_797_);
lean_ctor_set(v___x_787_, 0, v___x_795_);
v___x_799_ = v___x_787_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_797_);
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
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__1___boxed(lean_object* v_buf_815_, lean_object* v_name_816_, lean_object* v_value_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Http_Trailer_instEncodeV11___lam__1(v_buf_815_, v_name_816_, v_value_817_);
lean_dec_ref(v_value_817_);
return v_res_818_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Std_Http_Trailer_instEncodeV11___lam__2___closed__0));
v___x_821_ = lean_string_to_utf8(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1);
v___x_823_ = lean_byte_array_size(v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_825_ = lean_byte_array_size(v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2(lean_object* v___f_826_, lean_object* v_buffer_827_, lean_object* v_trailer_828_){
_start:
{
lean_object* v_data_829_; lean_object* v_size_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_855_; 
v_data_829_ = lean_ctor_get(v_buffer_827_, 0);
v_size_830_ = lean_ctor_get(v_buffer_827_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_buffer_827_);
if (v_isSharedCheck_855_ == 0)
{
v___x_832_ = v_buffer_827_;
v_isShared_833_ = v_isSharedCheck_855_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_size_830_);
lean_inc(v_data_829_);
lean_dec(v_buffer_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_855_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_834_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__1);
v___x_835_ = lean_array_push(v_data_829_, v___x_834_);
v___x_836_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__2);
v___x_837_ = lean_nat_add(v_size_830_, v___x_836_);
lean_dec(v_size_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_837_);
lean_ctor_set(v___x_832_, 0, v___x_835_);
v___x_839_ = v___x_832_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_837_);
v___x_839_ = v_reuseFailAlloc_854_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; lean_object* v_data_841_; lean_object* v_size_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_853_; 
v___x_840_ = l_Std_Http_Headers_fold___redArg(v_trailer_828_, v___x_839_, v___f_826_);
v_data_841_ = lean_ctor_get(v___x_840_, 0);
v_size_842_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_853_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_853_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_size_842_);
lean_inc(v_data_841_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_853_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_846_ = lean_obj_once(&l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11, &l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11_once, _init_l_Std_Http_Chunk_instEncodeV11___lam__2___closed__11);
v___x_847_ = lean_array_push(v_data_841_, v___x_846_);
v___x_848_ = lean_obj_once(&l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3, &l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3_once, _init_l_Std_Http_Trailer_instEncodeV11___lam__2___closed__3);
v___x_849_ = lean_nat_add(v_size_842_, v___x_848_);
lean_dec(v_size_842_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_849_);
lean_ctor_set(v___x_844_, 0, v___x_847_);
v___x_851_ = v___x_844_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Trailer_instEncodeV11___lam__2___boxed(lean_object* v___f_856_, lean_object* v_buffer_857_, lean_object* v_trailer_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_Http_Trailer_instEncodeV11___lam__2(v___f_856_, v_buffer_857_, v_trailer_858_);
lean_dec_ref(v_trailer_858_);
return v_res_859_;
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
