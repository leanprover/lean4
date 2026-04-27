// Lean compiler output
// Module: Std.Http.Protocol.H1.Reader
// Imports: public import Std.Time public import Std.Http.Data public import Std.Http.Internal public import Std.Http.Protocol.H1.Parser public import Std.Http.Protocol.H1.Config public import Std.Http.Protocol.H1.Message public import Std.Http.Protocol.H1.Error
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Std_Http_Chunk_instBEqExtensionName_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Chunk_instBEqExtensionValue_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Protocol_H1_instBEqError_beq(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_mkIterator(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Http_Chunk_instReprExtensionName_repr___redArg(lean_object*);
lean_object* l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instInhabitedBodyState_default___closed__0_value;
static const lean_string_object l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1 = (const lean_object*)&l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1_value;
static const lean_string_object l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2 = (const lean_object*)&l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3 = (const lean_object*)&l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3_value;
static const lean_string_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5;
static lean_once_cell_t l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__4_value)}};
static const lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8 = (const lean_object*)&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value;
static lean_once_cell_t l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2;
static lean_once_cell_t l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5_value;
static const lean_string_object l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__6_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Std.Http.Protocol.H1.Reader.BodyState.chunkedSize"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Std.Http.Protocol.H1.Reader.BodyState.closeDelimited"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Std.Http.Protocol.H1.Reader.BodyState.fixed"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6_value;
static lean_once_cell_t l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7;
static lean_once_cell_t l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Std.Http.Protocol.H1.Reader.BodyState.chunkedBody"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__9_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object*);
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Reader.State.closed"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Reader.State.complete"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Std.Http.Protocol.H1.Reader.State.pending"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Std.Http.Protocol.H1.Reader.State.needStartLine"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Std.Http.Protocol.H1.Reader.State.needHeader"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Reader.State.readBody"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__11_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Http.Protocol.H1.Reader.State.continue"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Http.Protocol.H1.Reader.State.failed"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__17_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_addHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_addHeader___closed__0_value;
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_addHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___closed__1 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_addHeader___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
switch(lean_obj_tag(v_t_8_))
{
case 0:
{
lean_object* v_remaining_10_; lean_object* v___x_11_; 
v_remaining_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_remaining_10_);
lean_dec_ref(v_t_8_);
v___x_11_ = lean_apply_1(v_k_9_, v_remaining_10_);
return v___x_11_;
}
case 2:
{
lean_object* v_ext_12_; lean_object* v_remaining_13_; lean_object* v___x_14_; 
v_ext_12_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_ext_12_);
v_remaining_13_ = lean_ctor_get(v_t_8_, 1);
lean_inc(v_remaining_13_);
lean_dec_ref(v_t_8_);
v___x_14_ = lean_apply_2(v_k_9_, v_ext_12_, v_remaining_13_);
return v___x_14_;
}
default: 
{
lean_dec(v_t_8_);
return v_k_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim___redArg(lean_object* v_t_27_, lean_object* v_fixed_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_27_, v_fixed_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_fixed_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_31_, v_fixed_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim___redArg(lean_object* v_t_35_, lean_object* v_chunkedSize_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_35_, v_chunkedSize_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_chunkedSize_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_39_, v_chunkedSize_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim___redArg(lean_object* v_t_43_, lean_object* v_chunkedBody_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_43_, v_chunkedBody_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_chunkedBody_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_47_, v_chunkedBody_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim___redArg(lean_object* v_t_51_, lean_object* v_closeDelimited_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_51_, v_closeDelimited_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_closeDelimited_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_55_, v_closeDelimited_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_71_; 
v___x_71_ = ((lean_object*)(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_val_72_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v_x_69_);
v___x_73_ = ((lean_object*)(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3));
v___x_74_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_val_72_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = l_Repr_addAppParen(v___x_75_, v_x_70_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_x_77_, v_x_78_);
lean_dec(v_x_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_dec(v_x_80_);
return v_x_81_;
}
else
{
lean_object* v_head_83_; lean_object* v_tail_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_93_; 
v_head_83_ = lean_ctor_get(v_x_82_, 0);
v_tail_84_ = lean_ctor_get(v_x_82_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_93_ == 0)
{
v___x_86_ = v_x_82_;
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_tail_84_);
lean_inc(v_head_83_);
lean_dec(v_x_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
lean_inc(v_x_80_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 5);
lean_ctor_set(v___x_86_, 1, v_x_80_);
lean_ctor_set(v___x_86_, 0, v_x_81_);
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_x_81_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_x_80_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_head_83_);
v_x_81_ = v___x_90_;
v_x_82_ = v_tail_84_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
if (lean_obj_tag(v_x_94_) == 0)
{
lean_object* v___x_96_; 
lean_dec(v_x_95_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v_tail_97_; 
v_tail_97_ = lean_ctor_get(v_x_94_, 1);
if (lean_obj_tag(v_tail_97_) == 0)
{
lean_object* v_head_98_; 
lean_dec(v_x_95_);
v_head_98_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_head_98_);
lean_dec_ref(v_x_94_);
return v_head_98_;
}
else
{
lean_object* v_head_99_; lean_object* v___x_100_; 
lean_inc(v_tail_97_);
v_head_99_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_head_99_);
lean_dec_ref(v_x_94_);
v___x_100_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(v_x_95_, v_head_99_, v_tail_97_);
return v___x_100_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0));
v___x_110_ = lean_string_length(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5);
v___x_112_ = lean_nat_to_int(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(lean_object* v_x_117_){
_start:
{
lean_object* v_fst_118_; lean_object* v_snd_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_142_; 
v_fst_118_ = lean_ctor_get(v_x_117_, 0);
v_snd_119_ = lean_ctor_get(v_x_117_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_117_);
if (v_isSharedCheck_142_ == 0)
{
v___x_121_ = v_x_117_;
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snd_119_);
lean_inc(v_fst_118_);
lean_dec(v_x_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_142_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_fst_118_);
v___x_125_ = lean_box(0);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 1);
lean_ctor_set(v___x_121_, 1, v___x_125_);
lean_ctor_set(v___x_121_, 0, v___x_124_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_141_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; 
v___x_128_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_snd_119_, v___x_123_);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
v___x_130_ = l_List_reverse___redArg(v___x_129_);
v___x_131_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3));
v___x_132_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(v___x_130_, v___x_131_);
v___x_133_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6);
v___x_134_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7));
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_132_);
v___x_136_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8));
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_133_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = 0;
v___x_140_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*1, v___x_139_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_dec(v_x_143_);
return v_x_144_;
}
else
{
lean_object* v_head_146_; lean_object* v_tail_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_157_; 
v_head_146_ = lean_ctor_get(v_x_145_, 0);
v_tail_147_ = lean_ctor_get(v_x_145_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_157_ == 0)
{
v___x_149_ = v_x_145_;
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_tail_147_);
lean_inc(v_head_146_);
lean_dec(v_x_145_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
lean_inc(v_x_143_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 5);
lean_ctor_set(v___x_149_, 1, v_x_143_);
lean_ctor_set(v___x_149_, 0, v_x_144_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_x_144_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_x_143_);
v___x_152_ = v_reuseFailAlloc_156_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_146_);
v___x_154_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v_x_144_ = v___x_154_;
v_x_145_ = v_tail_147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_dec(v_x_158_);
return v_x_159_;
}
else
{
lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
v_head_161_ = lean_ctor_get(v_x_160_, 0);
v_tail_162_ = lean_ctor_get(v_x_160_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v_x_160_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_tail_162_);
lean_inc(v_head_161_);
lean_dec(v_x_160_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
lean_inc(v_x_158_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 5);
lean_ctor_set(v___x_164_, 1, v_x_158_);
lean_ctor_set(v___x_164_, 0, v_x_159_);
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_x_159_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_x_158_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_161_);
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(v_x_158_, v___x_169_, v_tail_162_);
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_175_; 
lean_dec(v_x_174_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_tail_176_; 
v_tail_176_ = lean_ctor_get(v_x_173_, 1);
if (lean_obj_tag(v_tail_176_) == 0)
{
lean_object* v_head_177_; lean_object* v___x_178_; 
lean_dec(v_x_174_);
v_head_177_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_177_);
lean_dec_ref(v_x_173_);
v___x_178_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_177_);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v_tail_176_);
v_head_179_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_179_);
lean_dec_ref(v_x_173_);
v___x_180_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_179_);
v___x_181_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(v_x_174_, v___x_180_, v_tail_176_);
return v___x_181_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0));
v___x_185_ = lean_string_length(v___x_184_);
return v___x_185_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2);
v___x_187_ = lean_nat_to_int(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(lean_object* v_xs_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_196_ = lean_array_get_size(v_xs_195_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_eq(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_199_ = lean_array_to_list(v_xs_195_);
v___x_200_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3));
v___x_201_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(v___x_199_, v___x_200_);
v___x_202_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3);
v___x_203_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4));
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v___x_201_);
v___x_205_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5));
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_202_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = l_Std_Format_fill(v___x_207_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; 
lean_dec_ref(v_xs_195_);
v___x_209_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7));
return v___x_209_;
}
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = lean_nat_to_int(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_to_int(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(lean_object* v_x_232_, lean_object* v_prec_233_){
_start:
{
lean_object* v___y_235_; lean_object* v___y_242_; 
switch(lean_obj_tag(v_x_232_))
{
case 0:
{
lean_object* v_remaining_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_268_; 
v_remaining_248_ = lean_ctor_get(v_x_232_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_268_ == 0)
{
v___x_250_ = v_x_232_;
v_isShared_251_ = v_isSharedCheck_268_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_remaining_248_);
lean_dec(v_x_232_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_268_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___y_253_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1024u);
v___x_265_ = lean_nat_dec_le(v___x_264_, v_prec_233_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_253_ = v___x_266_;
goto v___jp_252_;
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_253_ = v___x_267_;
goto v___jp_252_;
}
v___jp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6));
v___x_255_ = l_Nat_reprFast(v_remaining_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 3);
lean_ctor_set(v___x_250_, 0, v___x_255_);
v___x_257_ = v___x_250_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_263_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_254_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
lean_inc(v___y_253_);
v___x_259_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_259_, 0, v___y_253_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = 0;
v___x_261_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set_uint8(v___x_261_, sizeof(void*)*1, v___x_260_);
v___x_262_ = l_Repr_addAppParen(v___x_261_, v_prec_233_);
return v___x_262_;
}
}
}
}
case 1:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1024u);
v___x_270_ = lean_nat_dec_le(v___x_269_, v_prec_233_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_235_ = v___x_271_;
goto v___jp_234_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_235_ = v___x_272_;
goto v___jp_234_;
}
}
case 2:
{
lean_object* v_ext_273_; lean_object* v_remaining_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_298_; 
v_ext_273_ = lean_ctor_get(v_x_232_, 0);
v_remaining_274_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_298_ == 0)
{
v___x_276_ = v_x_232_;
v_isShared_277_ = v_isSharedCheck_298_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_remaining_274_);
lean_inc(v_ext_273_);
lean_dec(v_x_232_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_298_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___y_279_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(1024u);
v___x_295_ = lean_nat_dec_le(v___x_294_, v_prec_233_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_279_ = v___x_296_;
goto v___jp_278_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_279_ = v___x_297_;
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_280_ = lean_box(1);
v___x_281_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11));
v___x_282_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(v_ext_273_);
if (v_isShared_277_ == 0)
{
lean_ctor_set_tag(v___x_276_, 5);
lean_ctor_set(v___x_276_, 1, v___x_282_);
lean_ctor_set(v___x_276_, 0, v___x_281_);
v___x_284_ = v___x_276_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_293_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_280_);
v___x_286_ = l_Nat_reprFast(v_remaining_274_);
v___x_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_285_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
lean_inc(v___y_279_);
v___x_289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_289_, 0, v___y_279_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = 0;
v___x_291_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___x_290_);
v___x_292_ = l_Repr_addAppParen(v___x_291_, v_prec_233_);
return v___x_292_;
}
}
}
}
default: 
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_233_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_242_ = v___x_301_;
goto v___jp_241_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_242_ = v___x_302_;
goto v___jp_241_;
}
}
}
v___jp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_236_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1));
lean_inc(v___y_235_);
v___x_237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_237_, 0, v___y_235_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = 0;
v___x_239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_238_);
v___x_240_ = l_Repr_addAppParen(v___x_239_, v_prec_233_);
return v___x_240_;
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3));
lean_inc(v___y_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___y_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = l_Repr_addAppParen(v___x_246_, v_prec_233_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed(lean_object* v_x_303_, lean_object* v_prec_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_x_303_, v_prec_304_);
lean_dec(v_prec_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_nat_to_int(v_a_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_x_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(v_x_311_, v_x_312_);
lean_dec(v_x_312_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
if (lean_obj_tag(v_x_317_) == 0)
{
uint8_t v___x_318_; 
v___x_318_ = 1;
return v___x_318_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
}
else
{
if (lean_obj_tag(v_x_317_) == 0)
{
uint8_t v___x_320_; 
v___x_320_ = 0;
return v___x_320_;
}
else
{
lean_object* v_val_321_; lean_object* v_val_322_; uint8_t v___x_323_; 
v_val_321_ = lean_ctor_get(v_x_316_, 0);
v_val_322_ = lean_ctor_get(v_x_317_, 0);
v___x_323_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_val_321_, v_val_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_x_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec(v_x_324_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(lean_object* v_xs_328_, lean_object* v_ys_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_zero_331_; uint8_t v_isZero_332_; 
v_zero_331_ = lean_unsigned_to_nat(0u);
v_isZero_332_ = lean_nat_dec_eq(v_x_330_, v_zero_331_);
if (v_isZero_332_ == 1)
{
lean_dec(v_x_330_);
return v_isZero_332_;
}
else
{
lean_object* v_one_333_; lean_object* v_n_334_; uint8_t v___y_336_; lean_object* v___x_338_; lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; uint8_t v___x_344_; 
v_one_333_ = lean_unsigned_to_nat(1u);
v_n_334_ = lean_nat_sub(v_x_330_, v_one_333_);
lean_dec(v_x_330_);
v___x_338_ = lean_array_fget_borrowed(v_xs_328_, v_n_334_);
v_fst_339_ = lean_ctor_get(v___x_338_, 0);
v_snd_340_ = lean_ctor_get(v___x_338_, 1);
v___x_341_ = lean_array_fget_borrowed(v_ys_329_, v_n_334_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
v_snd_343_ = lean_ctor_get(v___x_341_, 1);
v___x_344_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_fst_339_, v_fst_342_);
if (v___x_344_ == 0)
{
v___y_336_ = v___x_344_;
goto v___jp_335_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = l_Option_instBEq_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_snd_340_, v_snd_343_);
v___y_336_ = v___x_345_;
goto v___jp_335_;
}
v___jp_335_:
{
if (v___y_336_ == 0)
{
lean_dec(v_n_334_);
return v___y_336_;
}
else
{
v_x_330_ = v_n_334_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object* v_xs_346_, lean_object* v_ys_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_346_, v_ys_347_, v_x_348_);
lean_dec_ref(v_ys_347_);
lean_dec_ref(v_xs_346_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
switch(lean_obj_tag(v_x_351_))
{
case 0:
{
if (lean_obj_tag(v_x_352_) == 0)
{
lean_object* v_remaining_353_; lean_object* v_remaining_354_; uint8_t v___x_355_; 
v_remaining_353_ = lean_ctor_get(v_x_351_, 0);
v_remaining_354_ = lean_ctor_get(v_x_352_, 0);
v___x_355_ = lean_nat_dec_eq(v_remaining_353_, v_remaining_354_);
return v___x_355_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
}
case 1:
{
if (lean_obj_tag(v_x_352_) == 1)
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
case 2:
{
if (lean_obj_tag(v_x_352_) == 2)
{
lean_object* v_ext_359_; lean_object* v_remaining_360_; lean_object* v_ext_361_; lean_object* v_remaining_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v_ext_359_ = lean_ctor_get(v_x_351_, 0);
v_remaining_360_ = lean_ctor_get(v_x_351_, 1);
v_ext_361_ = lean_ctor_get(v_x_352_, 0);
v_remaining_362_ = lean_ctor_get(v_x_352_, 1);
v___x_363_ = lean_array_get_size(v_ext_359_);
v___x_364_ = lean_array_get_size(v_ext_361_);
v___x_365_ = lean_nat_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
return v___x_365_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_ext_359_, v_ext_361_, v___x_363_);
if (v___x_366_ == 0)
{
return v___x_366_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_eq(v_remaining_360_, v_remaining_362_);
return v___x_367_;
}
}
}
else
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
}
default: 
{
if (lean_obj_tag(v_x_352_) == 3)
{
uint8_t v___x_369_; 
v___x_369_ = 1;
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object* v_xs_375_, lean_object* v_ys_376_, lean_object* v_hsz_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_375_, v_ys_376_, v_x_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object* v_xs_381_, lean_object* v_ys_382_, lean_object* v_hsz_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(v_xs_381_, v_ys_382_, v_hsz_383_, v_x_384_, v_x_385_);
lean_dec_ref(v_ys_382_);
lean_dec_ref(v_xs_381_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(lean_object* v_x_390_){
_start:
{
switch(lean_obj_tag(v_x_390_))
{
case 0:
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(0u);
return v___x_391_;
}
case 1:
{
lean_object* v___x_392_; 
v___x_392_ = lean_unsigned_to_nat(1u);
return v___x_392_;
}
case 2:
{
lean_object* v___x_393_; 
v___x_393_ = lean_unsigned_to_nat(2u);
return v___x_393_;
}
case 3:
{
lean_object* v___x_394_; 
v___x_394_ = lean_unsigned_to_nat(3u);
return v___x_394_;
}
case 4:
{
lean_object* v___x_395_; 
v___x_395_ = lean_unsigned_to_nat(4u);
return v___x_395_;
}
case 5:
{
lean_object* v___x_396_; 
v___x_396_ = lean_unsigned_to_nat(5u);
return v___x_396_;
}
case 6:
{
lean_object* v___x_397_; 
v___x_397_ = lean_unsigned_to_nat(6u);
return v___x_397_;
}
default: 
{
lean_object* v___x_398_; 
v___x_398_ = lean_unsigned_to_nat(7u);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg___boxed(lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(v_x_399_);
lean_dec(v_x_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx(uint8_t v_dir_401_, lean_object* v_x_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___redArg(v_x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___boxed(lean_object* v_dir_404_, lean_object* v_x_405_){
_start:
{
uint8_t v_dir_boxed_406_; lean_object* v_res_407_; 
v_dir_boxed_406_ = lean_unbox(v_dir_404_);
v_res_407_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx(v_dir_boxed_406_, v_x_405_);
lean_dec(v_x_405_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(lean_object* v_t_408_, lean_object* v_k_409_){
_start:
{
switch(lean_obj_tag(v_t_408_))
{
case 1:
{
lean_object* v_a_410_; lean_object* v___x_411_; 
v_a_410_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v_t_408_);
v___x_411_ = lean_apply_1(v_k_409_, v_a_410_);
return v___x_411_;
}
case 2:
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v_t_408_);
v___x_413_ = lean_apply_1(v_k_409_, v_a_412_);
return v___x_413_;
}
case 3:
{
lean_object* v_a_414_; lean_object* v___x_415_; 
v_a_414_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_a_414_);
lean_dec_ref(v_t_408_);
v___x_415_ = lean_apply_1(v_k_409_, v_a_414_);
return v___x_415_;
}
case 7:
{
lean_object* v_error_416_; lean_object* v___x_417_; 
v_error_416_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_error_416_);
lean_dec_ref(v_t_408_);
v___x_417_ = lean_apply_1(v_k_409_, v_error_416_);
return v___x_417_;
}
default: 
{
lean_dec(v_t_408_);
return v_k_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t v_dir_418_, lean_object* v_motive_419_, lean_object* v_ctorIdx_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_k_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_421_, v_k_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object* v_dir_425_, lean_object* v_motive_426_, lean_object* v_ctorIdx_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_k_430_){
_start:
{
uint8_t v_dir_boxed_431_; lean_object* v_res_432_; 
v_dir_boxed_431_ = lean_unbox(v_dir_425_);
v_res_432_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_boxed_431_, v_motive_426_, v_ctorIdx_427_, v_t_428_, v_h_429_, v_k_430_);
lean_dec(v_ctorIdx_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object* v_t_433_, lean_object* v_needStartLine_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_433_, v_needStartLine_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t v_dir_436_, lean_object* v_motive_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_needStartLine_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_438_, v_needStartLine_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object* v_dir_442_, lean_object* v_motive_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_needStartLine_446_){
_start:
{
uint8_t v_dir_boxed_447_; lean_object* v_res_448_; 
v_dir_boxed_447_ = lean_unbox(v_dir_442_);
v_res_448_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_boxed_447_, v_motive_443_, v_t_444_, v_h_445_, v_needStartLine_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object* v_t_449_, lean_object* v_needHeader_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_449_, v_needHeader_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t v_dir_452_, lean_object* v_motive_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_needHeader_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_454_, v_needHeader_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object* v_dir_458_, lean_object* v_motive_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_needHeader_462_){
_start:
{
uint8_t v_dir_boxed_463_; lean_object* v_res_464_; 
v_dir_boxed_463_ = lean_unbox(v_dir_458_);
v_res_464_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_boxed_463_, v_motive_459_, v_t_460_, v_h_461_, v_needHeader_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object* v_t_465_, lean_object* v_readBody_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_465_, v_readBody_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t v_dir_468_, lean_object* v_motive_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_readBody_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_470_, v_readBody_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object* v_dir_474_, lean_object* v_motive_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_readBody_478_){
_start:
{
uint8_t v_dir_boxed_479_; lean_object* v_res_480_; 
v_dir_boxed_479_ = lean_unbox(v_dir_474_);
v_res_480_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_boxed_479_, v_motive_475_, v_t_476_, v_h_477_, v_readBody_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object* v_t_481_, lean_object* v_continue_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_481_, v_continue_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t v_dir_484_, lean_object* v_motive_485_, lean_object* v_t_486_, lean_object* v_h_487_, lean_object* v_continue_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_486_, v_continue_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(lean_object* v_dir_490_, lean_object* v_motive_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_continue_494_){
_start:
{
uint8_t v_dir_boxed_495_; lean_object* v_res_496_; 
v_dir_boxed_495_ = lean_unbox(v_dir_490_);
v_res_496_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(v_dir_boxed_495_, v_motive_491_, v_t_492_, v_h_493_, v_continue_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(lean_object* v_t_497_, lean_object* v_pending_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_497_, v_pending_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t v_dir_500_, lean_object* v_motive_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_pending_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_502_, v_pending_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object* v_dir_506_, lean_object* v_motive_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_pending_510_){
_start:
{
uint8_t v_dir_boxed_511_; lean_object* v_res_512_; 
v_dir_boxed_511_ = lean_unbox(v_dir_506_);
v_res_512_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_boxed_511_, v_motive_507_, v_t_508_, v_h_509_, v_pending_510_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object* v_t_513_, lean_object* v_complete_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_513_, v_complete_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t v_dir_516_, lean_object* v_motive_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_complete_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_518_, v_complete_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object* v_dir_522_, lean_object* v_motive_523_, lean_object* v_t_524_, lean_object* v_h_525_, lean_object* v_complete_526_){
_start:
{
uint8_t v_dir_boxed_527_; lean_object* v_res_528_; 
v_dir_boxed_527_ = lean_unbox(v_dir_522_);
v_res_528_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_boxed_527_, v_motive_523_, v_t_524_, v_h_525_, v_complete_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object* v_t_529_, lean_object* v_closed_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_529_, v_closed_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t v_dir_532_, lean_object* v_motive_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_closed_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_534_, v_closed_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object* v_dir_538_, lean_object* v_motive_539_, lean_object* v_t_540_, lean_object* v_h_541_, lean_object* v_closed_542_){
_start:
{
uint8_t v_dir_boxed_543_; lean_object* v_res_544_; 
v_dir_boxed_543_ = lean_unbox(v_dir_538_);
v_res_544_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_boxed_543_, v_motive_539_, v_t_540_, v_h_541_, v_closed_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(lean_object* v_t_545_, lean_object* v_failed_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_545_, v_failed_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim(uint8_t v_dir_548_, lean_object* v_motive_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_failed_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_550_, v_failed_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(lean_object* v_dir_554_, lean_object* v_motive_555_, lean_object* v_t_556_, lean_object* v_h_557_, lean_object* v_failed_558_){
_start:
{
uint8_t v_dir_boxed_559_; lean_object* v_res_560_; 
v_dir_boxed_559_ = lean_unbox(v_dir_554_);
v_res_560_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(v_dir_boxed_559_, v_motive_555_, v_t_556_, v_h_557_, v_failed_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_563_){
_start:
{
uint8_t v_dir_boxed_564_; lean_object* v_res_565_; 
v_dir_boxed_564_ = lean_unbox(v_dir_563_);
v_res_565_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_box(0);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_568_){
_start:
{
uint8_t v_a_6__boxed_569_; lean_object* v_res_570_; 
v_a_6__boxed_569_ = lean_unbox(v_a_568_);
v_res_570_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_6__boxed_569_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_607_, lean_object* v_prec_608_){
_start:
{
lean_object* v___y_610_; lean_object* v___y_617_; lean_object* v___y_624_; lean_object* v___y_631_; 
switch(lean_obj_tag(v_x_607_))
{
case 0:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(1024u);
v___x_638_ = lean_nat_dec_le(v___x_637_, v_prec_608_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_631_ = v___x_639_;
goto v___jp_630_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_631_ = v___x_640_;
goto v___jp_630_;
}
}
case 1:
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_661_; 
v_a_641_ = lean_ctor_get(v_x_607_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_607_);
if (v_isSharedCheck_661_ == 0)
{
v___x_643_ = v_x_607_;
v_isShared_644_ = v_isSharedCheck_661_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v_x_607_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_661_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___y_646_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(1024u);
v___x_658_ = lean_nat_dec_le(v___x_657_, v_prec_608_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_646_ = v___x_659_;
goto v___jp_645_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_646_ = v___x_660_;
goto v___jp_645_;
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_647_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_648_ = l_Nat_reprFast(v_a_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 3);
lean_ctor_set(v___x_643_, 0, v___x_648_);
v___x_650_ = v___x_643_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_656_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_647_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
lean_inc(v___y_646_);
v___x_652_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_652_, 0, v___y_646_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = 0;
v___x_654_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*1, v___x_653_);
v___x_655_ = l_Repr_addAppParen(v___x_654_, v_prec_608_);
return v___x_655_;
}
}
}
}
case 2:
{
lean_object* v_a_662_; lean_object* v___y_664_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_a_662_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_a_662_);
lean_dec_ref(v_x_607_);
v___x_673_ = lean_unsigned_to_nat(1024u);
v___x_674_ = lean_nat_dec_le(v___x_673_, v_prec_608_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_664_ = v___x_675_;
goto v___jp_663_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_664_ = v___x_676_;
goto v___jp_663_;
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_665_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_666_ = lean_unsigned_to_nat(1024u);
v___x_667_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_662_, v___x_666_);
v___x_668_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_665_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
lean_inc(v___y_664_);
v___x_669_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_669_, 0, v___y_664_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = 0;
v___x_671_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*1, v___x_670_);
v___x_672_ = l_Repr_addAppParen(v___x_671_, v_prec_608_);
return v___x_672_;
}
}
case 3:
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v___y_680_; uint8_t v___x_688_; 
v_a_677_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v_x_607_);
v___x_678_ = lean_unsigned_to_nat(1024u);
v___x_688_ = lean_nat_dec_le(v___x_678_, v_prec_608_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_680_ = v___x_689_;
goto v___jp_679_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_680_ = v___x_690_;
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_681_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_682_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_677_, v___x_678_);
v___x_683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_inc(v___y_680_);
v___x_684_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_684_, 0, v___y_680_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = 0;
v___x_686_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*1, v___x_685_);
v___x_687_ = l_Repr_addAppParen(v___x_686_, v_prec_608_);
return v___x_687_;
}
}
case 4:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(1024u);
v___x_692_ = lean_nat_dec_le(v___x_691_, v_prec_608_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_624_ = v___x_693_;
goto v___jp_623_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_624_ = v___x_694_;
goto v___jp_623_;
}
}
case 5:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(1024u);
v___x_696_ = lean_nat_dec_le(v___x_695_, v_prec_608_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_617_ = v___x_697_;
goto v___jp_616_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_617_ = v___x_698_;
goto v___jp_616_;
}
}
case 6:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(1024u);
v___x_700_ = lean_nat_dec_le(v___x_699_, v_prec_608_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_610_ = v___x_701_;
goto v___jp_609_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_610_ = v___x_702_;
goto v___jp_609_;
}
}
default: 
{
lean_object* v_error_703_; lean_object* v___y_705_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_error_703_ = lean_ctor_get(v_x_607_, 0);
lean_inc(v_error_703_);
lean_dec_ref(v_x_607_);
v___x_714_ = lean_unsigned_to_nat(1024u);
v___x_715_ = lean_nat_dec_le(v___x_714_, v_prec_608_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_705_ = v___x_716_;
goto v___jp_704_;
}
else
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_705_ = v___x_717_;
goto v___jp_704_;
}
v___jp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_706_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19));
v___x_707_ = lean_unsigned_to_nat(1024u);
v___x_708_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_703_, v___x_707_);
v___x_709_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_706_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_inc(v___y_705_);
v___x_710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_710_, 0, v___y_705_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = 0;
v___x_712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*1, v___x_711_);
v___x_713_ = l_Repr_addAppParen(v___x_712_, v_prec_608_);
return v___x_713_;
}
}
}
v___jp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_611_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_610_);
v___x_612_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_612_, 0, v___y_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = 0;
v___x_614_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*1, v___x_613_);
v___x_615_ = l_Repr_addAppParen(v___x_614_, v_prec_608_);
return v___x_615_;
}
v___jp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_618_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_617_);
v___x_619_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_619_, 0, v___y_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = 0;
v___x_621_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*1, v___x_620_);
v___x_622_ = l_Repr_addAppParen(v___x_621_, v_prec_608_);
return v___x_622_;
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_625_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_624_);
v___x_626_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_626_, 0, v___y_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = 0;
v___x_628_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*1, v___x_627_);
v___x_629_ = l_Repr_addAppParen(v___x_628_, v_prec_608_);
return v___x_629_;
}
v___jp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_632_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_631_);
v___x_633_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_633_, 0, v___y_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = 0;
v___x_635_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*1, v___x_634_);
v___x_636_ = l_Repr_addAppParen(v___x_635_, v_prec_608_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_718_, lean_object* v_prec_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_718_, v_prec_719_);
lean_dec(v_prec_719_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_721_, lean_object* v_x_722_, lean_object* v_prec_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_722_, v_prec_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_725_, lean_object* v_x_726_, lean_object* v_prec_727_){
_start:
{
uint8_t v_dir_892__boxed_728_; lean_object* v_res_729_; 
v_dir_892__boxed_728_ = lean_unbox(v_dir_725_);
v_res_729_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_892__boxed_728_, v_x_726_, v_prec_727_);
lean_dec(v_prec_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(v_dir_730_);
v___x_732_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_733_){
_start:
{
uint8_t v_dir_5__boxed_734_; lean_object* v_res_735_; 
v_dir_5__boxed_734_ = lean_unbox(v_dir_733_);
v_res_735_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_734_);
return v_res_735_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
switch(lean_obj_tag(v_x_736_))
{
case 0:
{
if (lean_obj_tag(v_x_737_) == 0)
{
uint8_t v___x_738_; 
v___x_738_ = 1;
return v___x_738_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = 0;
return v___x_739_;
}
}
case 1:
{
if (lean_obj_tag(v_x_737_) == 1)
{
lean_object* v_a_740_; lean_object* v_a_741_; uint8_t v___x_742_; 
v_a_740_ = lean_ctor_get(v_x_736_, 0);
v_a_741_ = lean_ctor_get(v_x_737_, 0);
v___x_742_ = lean_nat_dec_eq(v_a_740_, v_a_741_);
return v___x_742_;
}
else
{
uint8_t v___x_743_; 
v___x_743_ = 0;
return v___x_743_;
}
}
case 2:
{
if (lean_obj_tag(v_x_737_) == 2)
{
lean_object* v_a_744_; lean_object* v_a_745_; uint8_t v___x_746_; 
v_a_744_ = lean_ctor_get(v_x_736_, 0);
v_a_745_ = lean_ctor_get(v_x_737_, 0);
v___x_746_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_744_, v_a_745_);
return v___x_746_;
}
else
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
case 3:
{
if (lean_obj_tag(v_x_737_) == 3)
{
lean_object* v_a_748_; lean_object* v_a_749_; 
v_a_748_ = lean_ctor_get(v_x_736_, 0);
v_a_749_ = lean_ctor_get(v_x_737_, 0);
v_x_736_ = v_a_748_;
v_x_737_ = v_a_749_;
goto _start;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
}
case 4:
{
if (lean_obj_tag(v_x_737_) == 4)
{
uint8_t v___x_752_; 
v___x_752_ = 1;
return v___x_752_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = 0;
return v___x_753_;
}
}
case 5:
{
if (lean_obj_tag(v_x_737_) == 5)
{
uint8_t v___x_754_; 
v___x_754_ = 1;
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
case 6:
{
if (lean_obj_tag(v_x_737_) == 6)
{
uint8_t v___x_756_; 
v___x_756_ = 1;
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
default: 
{
if (lean_obj_tag(v_x_737_) == 7)
{
lean_object* v_error_758_; lean_object* v_error_759_; uint8_t v___x_760_; 
v_error_758_ = lean_ctor_get(v_x_736_, 0);
v_error_759_ = lean_ctor_get(v_x_737_, 0);
v___x_760_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_error_758_, v_error_759_);
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
uint8_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_762_, v_x_763_);
lean_dec(v_x_763_);
lean_dec(v_x_762_);
v_r_765_ = lean_box(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_767_, v_x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
uint8_t v_dir_218__boxed_773_; uint8_t v_res_774_; lean_object* v_r_775_; 
v_dir_218__boxed_773_ = lean_unbox(v_dir_770_);
v_res_774_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_218__boxed_773_, v_x_771_, v_x_772_);
lean_dec(v_x_772_);
lean_dec(v_x_771_);
v_r_775_ = lean_box(v_res_774_);
return v_r_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_box(v_dir_776_);
v___x_778_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_779_){
_start:
{
uint8_t v_dir_5__boxed_780_; lean_object* v_res_781_; 
v_dir_5__boxed_780_ = lean_unbox(v_dir_779_);
v_res_781_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_780_);
return v_res_781_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_782_){
_start:
{
lean_object* v_state_783_; 
v_state_783_ = lean_ctor_get(v_reader_782_, 0);
if (lean_obj_tag(v_state_783_) == 6)
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = 0;
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_786_);
lean_dec_ref(v_reader_786_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_789_, lean_object* v_reader_790_){
_start:
{
lean_object* v_state_791_; 
v_state_791_ = lean_ctor_get(v_reader_790_, 0);
if (lean_obj_tag(v_state_791_) == 6)
{
uint8_t v___x_792_; 
v___x_792_ = 1;
return v___x_792_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = 0;
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_794_, lean_object* v_reader_795_){
_start:
{
uint8_t v_dir_boxed_796_; uint8_t v_res_797_; lean_object* v_r_798_; 
v_dir_boxed_796_ = lean_unbox(v_dir_794_);
v_res_797_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_796_, v_reader_795_);
lean_dec_ref(v_reader_795_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_799_){
_start:
{
lean_object* v_state_800_; 
v_state_800_ = lean_ctor_get(v_reader_799_, 0);
if (lean_obj_tag(v_state_800_) == 5)
{
uint8_t v___x_801_; 
v___x_801_ = 1;
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = 0;
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_803_){
_start:
{
uint8_t v_res_804_; lean_object* v_r_805_; 
v_res_804_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_803_);
lean_dec_ref(v_reader_803_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_806_, lean_object* v_reader_807_){
_start:
{
lean_object* v_state_808_; 
v_state_808_ = lean_ctor_get(v_reader_807_, 0);
if (lean_obj_tag(v_state_808_) == 5)
{
uint8_t v___x_809_; 
v___x_809_ = 1;
return v___x_809_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_811_, lean_object* v_reader_812_){
_start:
{
uint8_t v_dir_boxed_813_; uint8_t v_res_814_; lean_object* v_r_815_; 
v_dir_boxed_813_ = lean_unbox(v_dir_811_);
v_res_814_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_813_, v_reader_812_);
lean_dec_ref(v_reader_812_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object* v_reader_816_){
_start:
{
lean_object* v_state_817_; 
v_state_817_ = lean_ctor_get(v_reader_816_, 0);
if (lean_obj_tag(v_state_817_) == 7)
{
uint8_t v___x_818_; 
v___x_818_ = 1;
return v___x_818_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object* v_reader_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_820_);
lean_dec_ref(v_reader_820_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t v_dir_823_, lean_object* v_reader_824_){
_start:
{
lean_object* v_state_825_; 
v_state_825_ = lean_ctor_get(v_reader_824_, 0);
if (lean_obj_tag(v_state_825_) == 7)
{
uint8_t v___x_826_; 
v___x_826_ = 1;
return v___x_826_;
}
else
{
uint8_t v___x_827_; 
v___x_827_ = 0;
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object* v_dir_828_, lean_object* v_reader_829_){
_start:
{
uint8_t v_dir_boxed_830_; uint8_t v_res_831_; lean_object* v_r_832_; 
v_dir_boxed_830_ = lean_unbox(v_dir_828_);
v_res_831_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_830_, v_reader_829_);
lean_dec_ref(v_reader_829_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_833_, lean_object* v_reader_834_){
_start:
{
lean_object* v_input_835_; lean_object* v_state_836_; lean_object* v_messageHead_837_; lean_object* v_messageCount_838_; lean_object* v_bodyBytesRead_839_; lean_object* v_headerBytesRead_840_; uint8_t v_noMoreInput_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_862_; 
v_input_835_ = lean_ctor_get(v_reader_834_, 1);
v_state_836_ = lean_ctor_get(v_reader_834_, 0);
v_messageHead_837_ = lean_ctor_get(v_reader_834_, 2);
v_messageCount_838_ = lean_ctor_get(v_reader_834_, 3);
v_bodyBytesRead_839_ = lean_ctor_get(v_reader_834_, 4);
v_headerBytesRead_840_ = lean_ctor_get(v_reader_834_, 5);
v_noMoreInput_841_ = lean_ctor_get_uint8(v_reader_834_, sizeof(void*)*6);
v_isSharedCheck_862_ = !lean_is_exclusive(v_reader_834_);
if (v_isSharedCheck_862_ == 0)
{
v___x_843_ = v_reader_834_;
v_isShared_844_ = v_isSharedCheck_862_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_headerBytesRead_840_);
lean_inc(v_bodyBytesRead_839_);
lean_inc(v_messageCount_838_);
lean_inc(v_messageHead_837_);
lean_inc(v_input_835_);
lean_inc(v_state_836_);
lean_dec(v_reader_834_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_862_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v_array_845_; lean_object* v_idx_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_array_845_ = lean_ctor_get(v_input_835_, 0);
lean_inc_ref(v_array_845_);
v_idx_846_ = lean_ctor_get(v_input_835_, 1);
lean_inc(v_idx_846_);
lean_dec_ref(v_input_835_);
v___x_847_ = lean_byte_array_size(v_array_845_);
v___x_848_ = lean_nat_dec_le(v___x_847_, v_idx_846_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_849_ = l_ByteArray_extract(v_array_845_, v_idx_846_, v___x_847_);
lean_dec_ref(v_array_845_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_byte_array_size(v___x_849_);
v___x_852_ = lean_byte_array_size(v_data_833_);
v___x_853_ = lean_byte_array_copy_slice(v_data_833_, v___x_850_, v___x_849_, v___x_851_, v___x_852_, v___x_848_);
lean_dec_ref(v_data_833_);
v___x_854_ = l_ByteArray_mkIterator(v___x_853_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_854_);
v___x_856_ = v___x_843_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_state_836_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_messageHead_837_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_messageCount_838_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_bodyBytesRead_839_);
lean_ctor_set(v_reuseFailAlloc_857_, 5, v_headerBytesRead_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_857_, sizeof(void*)*6, v_noMoreInput_841_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_idx_846_);
lean_dec_ref(v_array_845_);
v___x_858_ = l_ByteArray_mkIterator(v_data_833_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_858_);
v___x_860_ = v___x_843_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_state_836_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_messageHead_837_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_messageCount_838_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_bodyBytesRead_839_);
lean_ctor_set(v_reuseFailAlloc_861_, 5, v_headerBytesRead_840_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*6, v_noMoreInput_841_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_863_, lean_object* v_data_864_, lean_object* v_reader_865_){
_start:
{
lean_object* v_input_866_; lean_object* v_state_867_; lean_object* v_messageHead_868_; lean_object* v_messageCount_869_; lean_object* v_bodyBytesRead_870_; lean_object* v_headerBytesRead_871_; uint8_t v_noMoreInput_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_893_; 
v_input_866_ = lean_ctor_get(v_reader_865_, 1);
v_state_867_ = lean_ctor_get(v_reader_865_, 0);
v_messageHead_868_ = lean_ctor_get(v_reader_865_, 2);
v_messageCount_869_ = lean_ctor_get(v_reader_865_, 3);
v_bodyBytesRead_870_ = lean_ctor_get(v_reader_865_, 4);
v_headerBytesRead_871_ = lean_ctor_get(v_reader_865_, 5);
v_noMoreInput_872_ = lean_ctor_get_uint8(v_reader_865_, sizeof(void*)*6);
v_isSharedCheck_893_ = !lean_is_exclusive(v_reader_865_);
if (v_isSharedCheck_893_ == 0)
{
v___x_874_ = v_reader_865_;
v_isShared_875_ = v_isSharedCheck_893_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_headerBytesRead_871_);
lean_inc(v_bodyBytesRead_870_);
lean_inc(v_messageCount_869_);
lean_inc(v_messageHead_868_);
lean_inc(v_input_866_);
lean_inc(v_state_867_);
lean_dec(v_reader_865_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_893_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_array_876_; lean_object* v_idx_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v_array_876_ = lean_ctor_get(v_input_866_, 0);
lean_inc_ref(v_array_876_);
v_idx_877_ = lean_ctor_get(v_input_866_, 1);
lean_inc(v_idx_877_);
lean_dec_ref(v_input_866_);
v___x_878_ = lean_byte_array_size(v_array_876_);
v___x_879_ = lean_nat_dec_le(v___x_878_, v_idx_877_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_880_ = l_ByteArray_extract(v_array_876_, v_idx_877_, v___x_878_);
lean_dec_ref(v_array_876_);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_byte_array_size(v___x_880_);
v___x_883_ = lean_byte_array_size(v_data_864_);
v___x_884_ = lean_byte_array_copy_slice(v_data_864_, v___x_881_, v___x_880_, v___x_882_, v___x_883_, v___x_879_);
lean_dec_ref(v_data_864_);
v___x_885_ = l_ByteArray_mkIterator(v___x_884_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_885_);
v___x_887_ = v___x_874_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_state_867_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_messageHead_868_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_messageCount_869_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_bodyBytesRead_870_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_headerBytesRead_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*6, v_noMoreInput_872_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_891_; 
lean_dec(v_idx_877_);
lean_dec_ref(v_array_876_);
v___x_889_ = l_ByteArray_mkIterator(v_data_864_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_889_);
v___x_891_ = v___x_874_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_state_867_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v_messageHead_868_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_messageCount_869_);
lean_ctor_set(v_reuseFailAlloc_892_, 4, v_bodyBytesRead_870_);
lean_ctor_set(v_reuseFailAlloc_892_, 5, v_headerBytesRead_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_892_, sizeof(void*)*6, v_noMoreInput_872_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_894_, lean_object* v_data_895_, lean_object* v_reader_896_){
_start:
{
uint8_t v_dir_boxed_897_; lean_object* v_res_898_; 
v_dir_boxed_897_ = lean_unbox(v_dir_894_);
v_res_898_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_897_, v_data_895_, v_reader_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_899_, lean_object* v_reader_900_){
_start:
{
lean_object* v_state_901_; lean_object* v_messageHead_902_; lean_object* v_messageCount_903_; lean_object* v_bodyBytesRead_904_; lean_object* v_headerBytesRead_905_; uint8_t v_noMoreInput_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_state_901_ = lean_ctor_get(v_reader_900_, 0);
v_messageHead_902_ = lean_ctor_get(v_reader_900_, 2);
v_messageCount_903_ = lean_ctor_get(v_reader_900_, 3);
v_bodyBytesRead_904_ = lean_ctor_get(v_reader_900_, 4);
v_headerBytesRead_905_ = lean_ctor_get(v_reader_900_, 5);
v_noMoreInput_906_ = lean_ctor_get_uint8(v_reader_900_, sizeof(void*)*6);
v_isSharedCheck_913_ = !lean_is_exclusive(v_reader_900_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_reader_900_, 1);
lean_dec(v_unused_914_);
v___x_908_ = v_reader_900_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_headerBytesRead_905_);
lean_inc(v_bodyBytesRead_904_);
lean_inc(v_messageCount_903_);
lean_inc(v_messageHead_902_);
lean_inc(v_state_901_);
lean_dec(v_reader_900_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_input_899_);
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_state_901_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_input_899_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_messageHead_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_messageCount_903_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_bodyBytesRead_904_);
lean_ctor_set(v_reuseFailAlloc_912_, 5, v_headerBytesRead_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*6, v_noMoreInput_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_915_, lean_object* v_input_916_, lean_object* v_reader_917_){
_start:
{
lean_object* v_state_918_; lean_object* v_messageHead_919_; lean_object* v_messageCount_920_; lean_object* v_bodyBytesRead_921_; lean_object* v_headerBytesRead_922_; uint8_t v_noMoreInput_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_state_918_ = lean_ctor_get(v_reader_917_, 0);
v_messageHead_919_ = lean_ctor_get(v_reader_917_, 2);
v_messageCount_920_ = lean_ctor_get(v_reader_917_, 3);
v_bodyBytesRead_921_ = lean_ctor_get(v_reader_917_, 4);
v_headerBytesRead_922_ = lean_ctor_get(v_reader_917_, 5);
v_noMoreInput_923_ = lean_ctor_get_uint8(v_reader_917_, sizeof(void*)*6);
v_isSharedCheck_930_ = !lean_is_exclusive(v_reader_917_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_reader_917_, 1);
lean_dec(v_unused_931_);
v___x_925_ = v_reader_917_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_headerBytesRead_922_);
lean_inc(v_bodyBytesRead_921_);
lean_inc(v_messageCount_920_);
lean_inc(v_messageHead_919_);
lean_inc(v_state_918_);
lean_dec(v_reader_917_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v_input_916_);
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_state_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_input_916_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_messageHead_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_messageCount_920_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_bodyBytesRead_921_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_headerBytesRead_922_);
lean_ctor_set_uint8(v_reuseFailAlloc_929_, sizeof(void*)*6, v_noMoreInput_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object* v_dir_932_, lean_object* v_input_933_, lean_object* v_reader_934_){
_start:
{
uint8_t v_dir_boxed_935_; lean_object* v_res_936_; 
v_dir_boxed_935_ = lean_unbox(v_dir_932_);
v_res_936_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_935_, v_input_933_, v_reader_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object* v_messageHead_937_, lean_object* v_reader_938_){
_start:
{
lean_object* v_state_939_; lean_object* v_input_940_; lean_object* v_messageCount_941_; lean_object* v_bodyBytesRead_942_; lean_object* v_headerBytesRead_943_; uint8_t v_noMoreInput_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_state_939_ = lean_ctor_get(v_reader_938_, 0);
v_input_940_ = lean_ctor_get(v_reader_938_, 1);
v_messageCount_941_ = lean_ctor_get(v_reader_938_, 3);
v_bodyBytesRead_942_ = lean_ctor_get(v_reader_938_, 4);
v_headerBytesRead_943_ = lean_ctor_get(v_reader_938_, 5);
v_noMoreInput_944_ = lean_ctor_get_uint8(v_reader_938_, sizeof(void*)*6);
v_isSharedCheck_951_ = !lean_is_exclusive(v_reader_938_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v_reader_938_, 2);
lean_dec(v_unused_952_);
v___x_946_ = v_reader_938_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_headerBytesRead_943_);
lean_inc(v_bodyBytesRead_942_);
lean_inc(v_messageCount_941_);
lean_inc(v_input_940_);
lean_inc(v_state_939_);
lean_dec(v_reader_938_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 2, v_messageHead_937_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_state_939_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_input_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_messageHead_937_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_messageCount_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_bodyBytesRead_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_headerBytesRead_943_);
lean_ctor_set_uint8(v_reuseFailAlloc_950_, sizeof(void*)*6, v_noMoreInput_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_953_, lean_object* v_messageHead_954_, lean_object* v_reader_955_){
_start:
{
lean_object* v_state_956_; lean_object* v_input_957_; lean_object* v_messageCount_958_; lean_object* v_bodyBytesRead_959_; lean_object* v_headerBytesRead_960_; uint8_t v_noMoreInput_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
v_state_956_ = lean_ctor_get(v_reader_955_, 0);
v_input_957_ = lean_ctor_get(v_reader_955_, 1);
v_messageCount_958_ = lean_ctor_get(v_reader_955_, 3);
v_bodyBytesRead_959_ = lean_ctor_get(v_reader_955_, 4);
v_headerBytesRead_960_ = lean_ctor_get(v_reader_955_, 5);
v_noMoreInput_961_ = lean_ctor_get_uint8(v_reader_955_, sizeof(void*)*6);
v_isSharedCheck_968_ = !lean_is_exclusive(v_reader_955_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; 
v_unused_969_ = lean_ctor_get(v_reader_955_, 2);
lean_dec(v_unused_969_);
v___x_963_ = v_reader_955_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_headerBytesRead_960_);
lean_inc(v_bodyBytesRead_959_);
lean_inc(v_messageCount_958_);
lean_inc(v_input_957_);
lean_inc(v_state_956_);
lean_dec(v_reader_955_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 2, v_messageHead_954_);
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_state_956_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_input_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_messageHead_954_);
lean_ctor_set(v_reuseFailAlloc_967_, 3, v_messageCount_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 4, v_bodyBytesRead_959_);
lean_ctor_set(v_reuseFailAlloc_967_, 5, v_headerBytesRead_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_967_, sizeof(void*)*6, v_noMoreInput_961_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_970_, lean_object* v_messageHead_971_, lean_object* v_reader_972_){
_start:
{
uint8_t v_dir_boxed_973_; lean_object* v_res_974_; 
v_dir_boxed_973_ = lean_unbox(v_dir_970_);
v_res_974_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_973_, v_messageHead_971_, v_reader_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(lean_object* v_i_975_, lean_object* v_x_976_){
_start:
{
if (lean_obj_tag(v_x_976_) == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_mk_empty_array_with_capacity(v___x_977_);
v___x_979_ = lean_array_push(v___x_978_, v_i_975_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
else
{
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_989_; 
v_val_981_ = lean_ctor_get(v_x_976_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_976_);
if (v_isSharedCheck_989_ == 0)
{
v___x_983_ = v_x_976_;
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v_x_976_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_989_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = lean_array_push(v_val_981_, v_i_975_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_985_);
v___x_987_ = v___x_983_;
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_992_, lean_object* v_name_993_, lean_object* v_value_994_, lean_object* v_reader_995_){
_start:
{
if (v_dir_992_ == 0)
{
lean_object* v_messageHead_996_; lean_object* v_state_997_; lean_object* v_input_998_; lean_object* v_messageCount_999_; lean_object* v_bodyBytesRead_1000_; lean_object* v_headerBytesRead_1001_; uint8_t v_noMoreInput_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1038_; 
v_messageHead_996_ = lean_ctor_get(v_reader_995_, 2);
v_state_997_ = lean_ctor_get(v_reader_995_, 0);
v_input_998_ = lean_ctor_get(v_reader_995_, 1);
v_messageCount_999_ = lean_ctor_get(v_reader_995_, 3);
v_bodyBytesRead_1000_ = lean_ctor_get(v_reader_995_, 4);
v_headerBytesRead_1001_ = lean_ctor_get(v_reader_995_, 5);
v_noMoreInput_1002_ = lean_ctor_get_uint8(v_reader_995_, sizeof(void*)*6);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_reader_995_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1004_ = v_reader_995_;
v_isShared_1005_ = v_isSharedCheck_1038_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_headerBytesRead_1001_);
lean_inc(v_bodyBytesRead_1000_);
lean_inc(v_messageCount_999_);
lean_inc(v_messageHead_996_);
lean_inc(v_input_998_);
lean_inc(v_state_997_);
lean_dec(v_reader_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1038_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
uint8_t v_method_1006_; uint8_t v_version_1007_; lean_object* v_uri_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1035_; 
v_method_1006_ = lean_ctor_get_uint8(v_messageHead_996_, sizeof(void*)*2);
v_version_1007_ = lean_ctor_get_uint8(v_messageHead_996_, sizeof(void*)*2 + 1);
v_uri_1008_ = lean_ctor_get(v_messageHead_996_, 0);
lean_inc(v_uri_1008_);
v___x_1009_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_992_, v_messageHead_996_);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_messageHead_996_);
if (v_isSharedCheck_1035_ == 0)
{
lean_object* v_unused_1036_; lean_object* v_unused_1037_; 
v_unused_1036_ = lean_ctor_get(v_messageHead_996_, 1);
lean_dec(v_unused_1036_);
v_unused_1037_ = lean_ctor_get(v_messageHead_996_, 0);
lean_dec(v_unused_1037_);
v___x_1011_ = v_messageHead_996_;
v_isShared_1012_ = v_isSharedCheck_1035_;
goto v_resetjp_1010_;
}
else
{
lean_dec(v_messageHead_996_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1035_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_entries_1013_; lean_object* v_indexes_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1034_; 
v_entries_1013_ = lean_ctor_get(v___x_1009_, 0);
v_indexes_1014_ = lean_ctor_get(v___x_1009_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1016_ = v___x_1009_;
v_isShared_1017_ = v_isSharedCheck_1034_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_indexes_1014_);
lean_inc(v_entries_1013_);
lean_dec(v___x_1009_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1034_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v_i_1020_; lean_object* v_f_1021_; lean_object* v___x_1022_; lean_object* v_entries_1023_; lean_object* v_indexes_1024_; lean_object* v___x_1026_; 
v___f_1018_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1019_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1020_ = lean_array_get_size(v_entries_1013_);
v_f_1021_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1021_, 0, v_i_1020_);
lean_inc_ref(v_name_993_);
v___x_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_name_993_);
lean_ctor_set(v___x_1022_, 1, v_value_994_);
v_entries_1023_ = lean_array_push(v_entries_1013_, v___x_1022_);
v_indexes_1024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1018_, v___f_1019_, v_indexes_1014_, v_name_993_, v_f_1021_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_indexes_1024_);
lean_ctor_set(v___x_1016_, 0, v_entries_1023_);
v___x_1026_ = v___x_1016_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_entries_1023_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_indexes_1024_);
v___x_1026_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1028_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v___x_1026_);
v___x_1028_ = v___x_1011_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_uri_1008_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1032_, sizeof(void*)*2, v_method_1006_);
lean_ctor_set_uint8(v_reuseFailAlloc_1032_, sizeof(void*)*2 + 1, v_version_1007_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 2, v___x_1028_);
v___x_1030_ = v___x_1004_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_state_997_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_input_998_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_messageCount_999_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v_bodyBytesRead_1000_);
lean_ctor_set(v_reuseFailAlloc_1031_, 5, v_headerBytesRead_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*6, v_noMoreInput_1002_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
}
else
{
lean_object* v_messageHead_1039_; lean_object* v_state_1040_; lean_object* v_input_1041_; lean_object* v_messageCount_1042_; lean_object* v_bodyBytesRead_1043_; lean_object* v_headerBytesRead_1044_; uint8_t v_noMoreInput_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1080_; 
v_messageHead_1039_ = lean_ctor_get(v_reader_995_, 2);
v_state_1040_ = lean_ctor_get(v_reader_995_, 0);
v_input_1041_ = lean_ctor_get(v_reader_995_, 1);
v_messageCount_1042_ = lean_ctor_get(v_reader_995_, 3);
v_bodyBytesRead_1043_ = lean_ctor_get(v_reader_995_, 4);
v_headerBytesRead_1044_ = lean_ctor_get(v_reader_995_, 5);
v_noMoreInput_1045_ = lean_ctor_get_uint8(v_reader_995_, sizeof(void*)*6);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_reader_995_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1047_ = v_reader_995_;
v_isShared_1048_ = v_isSharedCheck_1080_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_headerBytesRead_1044_);
lean_inc(v_bodyBytesRead_1043_);
lean_inc(v_messageCount_1042_);
lean_inc(v_messageHead_1039_);
lean_inc(v_input_1041_);
lean_inc(v_state_1040_);
lean_dec(v_reader_995_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1080_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_status_1049_; uint8_t v_version_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1077_; 
v_status_1049_ = lean_ctor_get(v_messageHead_1039_, 0);
lean_inc(v_status_1049_);
v_version_1050_ = lean_ctor_get_uint8(v_messageHead_1039_, sizeof(void*)*2);
v___x_1051_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_992_, v_messageHead_1039_);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_messageHead_1039_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1078_ = lean_ctor_get(v_messageHead_1039_, 1);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v_messageHead_1039_, 0);
lean_dec(v_unused_1079_);
v___x_1053_ = v_messageHead_1039_;
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v_messageHead_1039_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_entries_1055_; lean_object* v_indexes_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1076_; 
v_entries_1055_ = lean_ctor_get(v___x_1051_, 0);
v_indexes_1056_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1058_ = v___x_1051_;
v_isShared_1059_ = v_isSharedCheck_1076_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_indexes_1056_);
lean_inc(v_entries_1055_);
lean_dec(v___x_1051_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1076_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v_i_1062_; lean_object* v_f_1063_; lean_object* v___x_1064_; lean_object* v_entries_1065_; lean_object* v_indexes_1066_; lean_object* v___x_1068_; 
v___f_1060_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1061_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1062_ = lean_array_get_size(v_entries_1055_);
v_f_1063_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1063_, 0, v_i_1062_);
lean_inc_ref(v_name_993_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_name_993_);
lean_ctor_set(v___x_1064_, 1, v_value_994_);
v_entries_1065_ = lean_array_push(v_entries_1055_, v___x_1064_);
v_indexes_1066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1060_, v___f_1061_, v_indexes_1056_, v_name_993_, v_f_1063_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_indexes_1066_);
lean_ctor_set(v___x_1058_, 0, v_entries_1065_);
v___x_1068_ = v___x_1058_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_entries_1065_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_indexes_1066_);
v___x_1068_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v___x_1068_);
v___x_1070_ = v___x_1053_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_status_1049_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*2, v_version_1050_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 2, v___x_1070_);
v___x_1072_ = v___x_1047_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_state_1040_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_input_1041_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_messageCount_1042_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_bodyBytesRead_1043_);
lean_ctor_set(v_reuseFailAlloc_1073_, 5, v_headerBytesRead_1044_);
lean_ctor_set_uint8(v_reuseFailAlloc_1073_, sizeof(void*)*6, v_noMoreInput_1045_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1081_, lean_object* v_name_1082_, lean_object* v_value_1083_, lean_object* v_reader_1084_){
_start:
{
uint8_t v_dir_boxed_1085_; lean_object* v_res_1086_; 
v_dir_boxed_1085_ = lean_unbox(v_dir_1081_);
v_res_1086_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1085_, v_name_1082_, v_value_1083_, v_reader_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object* v_reader_1087_){
_start:
{
lean_object* v_input_1088_; lean_object* v_messageHead_1089_; lean_object* v_messageCount_1090_; lean_object* v_bodyBytesRead_1091_; lean_object* v_headerBytesRead_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1101_; 
v_input_1088_ = lean_ctor_get(v_reader_1087_, 1);
v_messageHead_1089_ = lean_ctor_get(v_reader_1087_, 2);
v_messageCount_1090_ = lean_ctor_get(v_reader_1087_, 3);
v_bodyBytesRead_1091_ = lean_ctor_get(v_reader_1087_, 4);
v_headerBytesRead_1092_ = lean_ctor_get(v_reader_1087_, 5);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_reader_1087_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_reader_1087_, 0);
lean_dec(v_unused_1102_);
v___x_1094_ = v_reader_1087_;
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_headerBytesRead_1092_);
lean_inc(v_bodyBytesRead_1091_);
lean_inc(v_messageCount_1090_);
lean_inc(v_messageHead_1089_);
lean_inc(v_input_1088_);
lean_dec(v_reader_1087_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1099_; 
v___x_1096_ = lean_box(6);
v___x_1097_ = 1;
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_input_1088_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_messageHead_1089_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_messageCount_1090_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v_bodyBytesRead_1091_);
lean_ctor_set(v_reuseFailAlloc_1100_, 5, v_headerBytesRead_1092_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*6, v___x_1097_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t v_dir_1103_, lean_object* v_reader_1104_){
_start:
{
lean_object* v_input_1105_; lean_object* v_messageHead_1106_; lean_object* v_messageCount_1107_; lean_object* v_bodyBytesRead_1108_; lean_object* v_headerBytesRead_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1118_; 
v_input_1105_ = lean_ctor_get(v_reader_1104_, 1);
v_messageHead_1106_ = lean_ctor_get(v_reader_1104_, 2);
v_messageCount_1107_ = lean_ctor_get(v_reader_1104_, 3);
v_bodyBytesRead_1108_ = lean_ctor_get(v_reader_1104_, 4);
v_headerBytesRead_1109_ = lean_ctor_get(v_reader_1104_, 5);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_reader_1104_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v_reader_1104_, 0);
lean_dec(v_unused_1119_);
v___x_1111_ = v_reader_1104_;
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_headerBytesRead_1109_);
lean_inc(v_bodyBytesRead_1108_);
lean_inc(v_messageCount_1107_);
lean_inc(v_messageHead_1106_);
lean_inc(v_input_1105_);
lean_dec(v_reader_1104_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1118_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; lean_object* v___x_1116_; 
v___x_1113_ = lean_box(6);
v___x_1114_ = 1;
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1113_);
v___x_1116_ = v___x_1111_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_input_1105_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_messageHead_1106_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_messageCount_1107_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_bodyBytesRead_1108_);
lean_ctor_set(v_reuseFailAlloc_1117_, 5, v_headerBytesRead_1109_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*6, v___x_1114_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object* v_dir_1120_, lean_object* v_reader_1121_){
_start:
{
uint8_t v_dir_boxed_1122_; lean_object* v_res_1123_; 
v_dir_boxed_1122_ = lean_unbox(v_dir_1120_);
v_res_1123_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_1122_, v_reader_1121_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1124_){
_start:
{
lean_object* v_input_1125_; lean_object* v_messageHead_1126_; lean_object* v_messageCount_1127_; lean_object* v_bodyBytesRead_1128_; lean_object* v_headerBytesRead_1129_; uint8_t v_noMoreInput_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1140_; 
v_input_1125_ = lean_ctor_get(v_reader_1124_, 1);
v_messageHead_1126_ = lean_ctor_get(v_reader_1124_, 2);
v_messageCount_1127_ = lean_ctor_get(v_reader_1124_, 3);
v_bodyBytesRead_1128_ = lean_ctor_get(v_reader_1124_, 4);
v_headerBytesRead_1129_ = lean_ctor_get(v_reader_1124_, 5);
v_noMoreInput_1130_ = lean_ctor_get_uint8(v_reader_1124_, sizeof(void*)*6);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_reader_1124_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v_reader_1124_, 0);
lean_dec(v_unused_1141_);
v___x_1132_ = v_reader_1124_;
v_isShared_1133_ = v_isSharedCheck_1140_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_headerBytesRead_1129_);
lean_inc(v_bodyBytesRead_1128_);
lean_inc(v_messageCount_1127_);
lean_inc(v_messageHead_1126_);
lean_inc(v_input_1125_);
lean_dec(v_reader_1124_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1140_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1134_ = lean_box(5);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_add(v_messageCount_1127_, v___x_1135_);
lean_dec(v_messageCount_1127_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 3, v___x_1136_);
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1138_ = v___x_1132_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_input_1125_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_messageHead_1126_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1139_, 4, v_bodyBytesRead_1128_);
lean_ctor_set(v_reuseFailAlloc_1139_, 5, v_headerBytesRead_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1139_, sizeof(void*)*6, v_noMoreInput_1130_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1142_, lean_object* v_reader_1143_){
_start:
{
lean_object* v_input_1144_; lean_object* v_messageHead_1145_; lean_object* v_messageCount_1146_; lean_object* v_bodyBytesRead_1147_; lean_object* v_headerBytesRead_1148_; uint8_t v_noMoreInput_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
v_input_1144_ = lean_ctor_get(v_reader_1143_, 1);
v_messageHead_1145_ = lean_ctor_get(v_reader_1143_, 2);
v_messageCount_1146_ = lean_ctor_get(v_reader_1143_, 3);
v_bodyBytesRead_1147_ = lean_ctor_get(v_reader_1143_, 4);
v_headerBytesRead_1148_ = lean_ctor_get(v_reader_1143_, 5);
v_noMoreInput_1149_ = lean_ctor_get_uint8(v_reader_1143_, sizeof(void*)*6);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_reader_1143_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_reader_1143_, 0);
lean_dec(v_unused_1160_);
v___x_1151_ = v_reader_1143_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_headerBytesRead_1148_);
lean_inc(v_bodyBytesRead_1147_);
lean_inc(v_messageCount_1146_);
lean_inc(v_messageHead_1145_);
lean_inc(v_input_1144_);
lean_dec(v_reader_1143_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1153_ = lean_box(5);
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_add(v_messageCount_1146_, v___x_1154_);
lean_dec(v_messageCount_1146_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 3, v___x_1155_);
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_input_1144_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_messageHead_1145_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_bodyBytesRead_1147_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v_headerBytesRead_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1158_, sizeof(void*)*6, v_noMoreInput_1149_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object* v_dir_1161_, lean_object* v_reader_1162_){
_start:
{
uint8_t v_dir_boxed_1163_; lean_object* v_res_1164_; 
v_dir_boxed_1163_ = lean_unbox(v_dir_1161_);
v_res_1164_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_1163_, v_reader_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object* v_error_1165_, lean_object* v_reader_1166_){
_start:
{
lean_object* v_input_1167_; lean_object* v_messageHead_1168_; lean_object* v_messageCount_1169_; lean_object* v_bodyBytesRead_1170_; lean_object* v_headerBytesRead_1171_; uint8_t v_noMoreInput_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_input_1167_ = lean_ctor_get(v_reader_1166_, 1);
v_messageHead_1168_ = lean_ctor_get(v_reader_1166_, 2);
v_messageCount_1169_ = lean_ctor_get(v_reader_1166_, 3);
v_bodyBytesRead_1170_ = lean_ctor_get(v_reader_1166_, 4);
v_headerBytesRead_1171_ = lean_ctor_get(v_reader_1166_, 5);
v_noMoreInput_1172_ = lean_ctor_get_uint8(v_reader_1166_, sizeof(void*)*6);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_reader_1166_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_reader_1166_, 0);
lean_dec(v_unused_1181_);
v___x_1174_ = v_reader_1166_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_headerBytesRead_1171_);
lean_inc(v_bodyBytesRead_1170_);
lean_inc(v_messageCount_1169_);
lean_inc(v_messageHead_1168_);
lean_inc(v_input_1167_);
lean_dec(v_reader_1166_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1176_, 0, v_error_1165_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_input_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_messageHead_1168_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_messageCount_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_bodyBytesRead_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_headerBytesRead_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*6, v_noMoreInput_1172_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t v_dir_1182_, lean_object* v_error_1183_, lean_object* v_reader_1184_){
_start:
{
lean_object* v_input_1185_; lean_object* v_messageHead_1186_; lean_object* v_messageCount_1187_; lean_object* v_bodyBytesRead_1188_; lean_object* v_headerBytesRead_1189_; uint8_t v_noMoreInput_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_input_1185_ = lean_ctor_get(v_reader_1184_, 1);
v_messageHead_1186_ = lean_ctor_get(v_reader_1184_, 2);
v_messageCount_1187_ = lean_ctor_get(v_reader_1184_, 3);
v_bodyBytesRead_1188_ = lean_ctor_get(v_reader_1184_, 4);
v_headerBytesRead_1189_ = lean_ctor_get(v_reader_1184_, 5);
v_noMoreInput_1190_ = lean_ctor_get_uint8(v_reader_1184_, sizeof(void*)*6);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_reader_1184_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_reader_1184_, 0);
lean_dec(v_unused_1199_);
v___x_1192_ = v_reader_1184_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_headerBytesRead_1189_);
lean_inc(v_bodyBytesRead_1188_);
lean_inc(v_messageCount_1187_);
lean_inc(v_messageHead_1186_);
lean_inc(v_input_1185_);
lean_dec(v_reader_1184_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_error_1183_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_input_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_messageHead_1186_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_messageCount_1187_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_bodyBytesRead_1188_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v_headerBytesRead_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*6, v_noMoreInput_1190_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object* v_dir_1200_, lean_object* v_error_1201_, lean_object* v_reader_1202_){
_start:
{
uint8_t v_dir_boxed_1203_; lean_object* v_res_1204_; 
v_dir_boxed_1203_ = lean_unbox(v_dir_1200_);
v_res_1204_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_1203_, v_error_1201_, v_reader_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1205_, lean_object* v_reader_1206_){
_start:
{
lean_object* v_input_1207_; lean_object* v_messageCount_1208_; uint8_t v_noMoreInput_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1219_; 
v_input_1207_ = lean_ctor_get(v_reader_1206_, 1);
v_messageCount_1208_ = lean_ctor_get(v_reader_1206_, 3);
v_noMoreInput_1209_ = lean_ctor_get_uint8(v_reader_1206_, sizeof(void*)*6);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_reader_1206_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1220_ = lean_ctor_get(v_reader_1206_, 5);
lean_dec(v_unused_1220_);
v_unused_1221_ = lean_ctor_get(v_reader_1206_, 4);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_reader_1206_, 2);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_reader_1206_, 0);
lean_dec(v_unused_1223_);
v___x_1211_ = v_reader_1206_;
v_isShared_1212_ = v_isSharedCheck_1219_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_messageCount_1208_);
lean_inc(v_input_1207_);
lean_dec(v_reader_1206_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1219_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1213_ = lean_box(0);
v___x_1214_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1205_);
v___x_1215_ = lean_unsigned_to_nat(0u);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 5, v___x_1215_);
lean_ctor_set(v___x_1211_, 4, v___x_1215_);
lean_ctor_set(v___x_1211_, 2, v___x_1214_);
lean_ctor_set(v___x_1211_, 0, v___x_1213_);
v___x_1217_ = v___x_1211_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_input_1207_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_messageCount_1208_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 5, v___x_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1218_, sizeof(void*)*6, v_noMoreInput_1209_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1224_, lean_object* v_reader_1225_){
_start:
{
uint8_t v_dir_boxed_1226_; lean_object* v_res_1227_; 
v_dir_boxed_1226_ = lean_unbox(v_dir_1224_);
v_res_1227_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1226_, v_reader_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1228_){
_start:
{
lean_object* v_state_1229_; lean_object* v_input_1230_; uint8_t v_noMoreInput_1231_; uint8_t v___y_1233_; lean_object* v_array_1238_; lean_object* v_idx_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_state_1229_ = lean_ctor_get(v_reader_1228_, 0);
v_input_1230_ = lean_ctor_get(v_reader_1228_, 1);
v_noMoreInput_1231_ = lean_ctor_get_uint8(v_reader_1228_, sizeof(void*)*6);
v_array_1238_ = lean_ctor_get(v_input_1230_, 0);
v_idx_1239_ = lean_ctor_get(v_input_1230_, 1);
v___x_1240_ = lean_byte_array_size(v_array_1238_);
v___x_1241_ = lean_nat_dec_le(v___x_1240_, v_idx_1239_);
if (v___x_1241_ == 0)
{
v___y_1233_ = v___x_1241_;
goto v___jp_1232_;
}
else
{
if (v_noMoreInput_1231_ == 0)
{
v___y_1233_ = v___x_1241_;
goto v___jp_1232_;
}
else
{
uint8_t v___x_1242_; 
v___x_1242_ = 0;
return v___x_1242_;
}
}
v___jp_1232_:
{
if (v___y_1233_ == 0)
{
return v___y_1233_;
}
else
{
switch(lean_obj_tag(v_state_1229_))
{
case 5:
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
return v___x_1234_;
}
case 6:
{
uint8_t v___x_1235_; 
v___x_1235_ = 0;
return v___x_1235_;
}
case 7:
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
return v___x_1236_;
}
case 3:
{
uint8_t v___x_1237_; 
v___x_1237_ = 0;
return v___x_1237_;
}
default: 
{
return v___y_1233_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1243_);
lean_dec_ref(v_reader_1243_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1246_, lean_object* v_reader_1247_){
_start:
{
lean_object* v_state_1248_; lean_object* v_input_1249_; uint8_t v_noMoreInput_1250_; uint8_t v___y_1252_; lean_object* v_array_1257_; lean_object* v_idx_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_state_1248_ = lean_ctor_get(v_reader_1247_, 0);
v_input_1249_ = lean_ctor_get(v_reader_1247_, 1);
v_noMoreInput_1250_ = lean_ctor_get_uint8(v_reader_1247_, sizeof(void*)*6);
v_array_1257_ = lean_ctor_get(v_input_1249_, 0);
v_idx_1258_ = lean_ctor_get(v_input_1249_, 1);
v___x_1259_ = lean_byte_array_size(v_array_1257_);
v___x_1260_ = lean_nat_dec_le(v___x_1259_, v_idx_1258_);
if (v___x_1260_ == 0)
{
v___y_1252_ = v___x_1260_;
goto v___jp_1251_;
}
else
{
if (v_noMoreInput_1250_ == 0)
{
v___y_1252_ = v___x_1260_;
goto v___jp_1251_;
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = 0;
return v___x_1261_;
}
}
v___jp_1251_:
{
if (v___y_1252_ == 0)
{
return v___y_1252_;
}
else
{
switch(lean_obj_tag(v_state_1248_))
{
case 5:
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
return v___x_1253_;
}
case 6:
{
uint8_t v___x_1254_; 
v___x_1254_ = 0;
return v___x_1254_;
}
case 7:
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
case 3:
{
uint8_t v___x_1256_; 
v___x_1256_ = 0;
return v___x_1256_;
}
default: 
{
return v___y_1252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1262_, lean_object* v_reader_1263_){
_start:
{
uint8_t v_dir_boxed_1264_; uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_dir_boxed_1264_ = lean_unbox(v_dir_1262_);
v_res_1265_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1264_, v_reader_1263_);
lean_dec_ref(v_reader_1263_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object* v_reader_1267_){
_start:
{
lean_object* v_state_1268_; 
v_state_1268_ = lean_ctor_get(v_reader_1267_, 0);
lean_inc(v_state_1268_);
lean_dec_ref(v_reader_1267_);
if (lean_obj_tag(v_state_1268_) == 7)
{
lean_object* v_error_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
v_error_1269_ = lean_ctor_get(v_state_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_state_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v_state_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_error_1269_);
lean_dec(v_state_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 1);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_error_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v___x_1277_; 
lean_dec(v_state_1268_);
v___x_1277_ = lean_box(0);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t v_dir_1278_, lean_object* v_reader_1279_){
_start:
{
lean_object* v_state_1280_; 
v_state_1280_ = lean_ctor_get(v_reader_1279_, 0);
lean_inc(v_state_1280_);
lean_dec_ref(v_reader_1279_);
if (lean_obj_tag(v_state_1280_) == 7)
{
lean_object* v_error_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_error_1281_ = lean_ctor_get(v_state_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_state_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v_state_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_error_1281_);
lean_dec(v_state_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 1);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_error_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v___x_1289_; 
lean_dec(v_state_1280_);
v___x_1289_ = lean_box(0);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object* v_dir_1290_, lean_object* v_reader_1291_){
_start:
{
uint8_t v_dir_boxed_1292_; lean_object* v_res_1293_; 
v_dir_boxed_1292_ = lean_unbox(v_dir_1290_);
v_res_1293_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_1292_, v_reader_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1294_){
_start:
{
lean_object* v_input_1295_; lean_object* v_array_1296_; lean_object* v_idx_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_input_1295_ = lean_ctor_get(v_reader_1294_, 1);
v_array_1296_ = lean_ctor_get(v_input_1295_, 0);
v_idx_1297_ = lean_ctor_get(v_input_1295_, 1);
v___x_1298_ = lean_byte_array_size(v_array_1296_);
v___x_1299_ = lean_nat_sub(v___x_1298_, v_idx_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1300_);
lean_dec_ref(v_reader_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1302_, lean_object* v_reader_1303_){
_start:
{
lean_object* v_input_1304_; lean_object* v_array_1305_; lean_object* v_idx_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_input_1304_ = lean_ctor_get(v_reader_1303_, 1);
v_array_1305_ = lean_ctor_get(v_input_1304_, 0);
v_idx_1306_ = lean_ctor_get(v_input_1304_, 1);
v___x_1307_ = lean_byte_array_size(v_array_1305_);
v___x_1308_ = lean_nat_sub(v___x_1307_, v_idx_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1309_, lean_object* v_reader_1310_){
_start:
{
uint8_t v_dir_boxed_1311_; lean_object* v_res_1312_; 
v_dir_boxed_1311_ = lean_unbox(v_dir_1309_);
v_res_1312_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1311_, v_reader_1310_);
lean_dec_ref(v_reader_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1313_, lean_object* v_reader_1314_){
_start:
{
lean_object* v_input_1315_; lean_object* v_state_1316_; lean_object* v_messageHead_1317_; lean_object* v_messageCount_1318_; lean_object* v_bodyBytesRead_1319_; lean_object* v_headerBytesRead_1320_; uint8_t v_noMoreInput_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1338_; 
v_input_1315_ = lean_ctor_get(v_reader_1314_, 1);
v_state_1316_ = lean_ctor_get(v_reader_1314_, 0);
v_messageHead_1317_ = lean_ctor_get(v_reader_1314_, 2);
v_messageCount_1318_ = lean_ctor_get(v_reader_1314_, 3);
v_bodyBytesRead_1319_ = lean_ctor_get(v_reader_1314_, 4);
v_headerBytesRead_1320_ = lean_ctor_get(v_reader_1314_, 5);
v_noMoreInput_1321_ = lean_ctor_get_uint8(v_reader_1314_, sizeof(void*)*6);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_reader_1314_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1323_ = v_reader_1314_;
v_isShared_1324_ = v_isSharedCheck_1338_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_headerBytesRead_1320_);
lean_inc(v_bodyBytesRead_1319_);
lean_inc(v_messageCount_1318_);
lean_inc(v_messageHead_1317_);
lean_inc(v_input_1315_);
lean_inc(v_state_1316_);
lean_dec(v_reader_1314_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1338_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_array_1325_; lean_object* v_idx_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1337_; 
v_array_1325_ = lean_ctor_get(v_input_1315_, 0);
v_idx_1326_ = lean_ctor_get(v_input_1315_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_input_1315_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1328_ = v_input_1315_;
v_isShared_1329_ = v_isSharedCheck_1337_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_idx_1326_);
lean_inc(v_array_1325_);
lean_dec(v_input_1315_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1337_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = lean_nat_add(v_idx_1326_, v_n_1313_);
lean_dec(v_idx_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 1, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_array_1325_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 1, v___x_1332_);
v___x_1334_ = v___x_1323_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_state_1316_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_messageHead_1317_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v_messageCount_1318_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_bodyBytesRead_1319_);
lean_ctor_set(v_reuseFailAlloc_1335_, 5, v_headerBytesRead_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1335_, sizeof(void*)*6, v_noMoreInput_1321_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1339_, lean_object* v_reader_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1339_, v_reader_1340_);
lean_dec(v_n_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1342_, lean_object* v_n_1343_, lean_object* v_reader_1344_){
_start:
{
lean_object* v_input_1345_; lean_object* v_state_1346_; lean_object* v_messageHead_1347_; lean_object* v_messageCount_1348_; lean_object* v_bodyBytesRead_1349_; lean_object* v_headerBytesRead_1350_; uint8_t v_noMoreInput_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1368_; 
v_input_1345_ = lean_ctor_get(v_reader_1344_, 1);
v_state_1346_ = lean_ctor_get(v_reader_1344_, 0);
v_messageHead_1347_ = lean_ctor_get(v_reader_1344_, 2);
v_messageCount_1348_ = lean_ctor_get(v_reader_1344_, 3);
v_bodyBytesRead_1349_ = lean_ctor_get(v_reader_1344_, 4);
v_headerBytesRead_1350_ = lean_ctor_get(v_reader_1344_, 5);
v_noMoreInput_1351_ = lean_ctor_get_uint8(v_reader_1344_, sizeof(void*)*6);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_reader_1344_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1353_ = v_reader_1344_;
v_isShared_1354_ = v_isSharedCheck_1368_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_headerBytesRead_1350_);
lean_inc(v_bodyBytesRead_1349_);
lean_inc(v_messageCount_1348_);
lean_inc(v_messageHead_1347_);
lean_inc(v_input_1345_);
lean_inc(v_state_1346_);
lean_dec(v_reader_1344_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1368_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_array_1355_; lean_object* v_idx_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1367_; 
v_array_1355_ = lean_ctor_get(v_input_1345_, 0);
v_idx_1356_ = lean_ctor_get(v_input_1345_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_input_1345_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1358_ = v_input_1345_;
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_idx_1356_);
lean_inc(v_array_1355_);
lean_dec(v_input_1345_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1367_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_nat_add(v_idx_1356_, v_n_1343_);
lean_dec(v_idx_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_array_1355_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1362_);
v___x_1364_ = v___x_1353_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_state_1346_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_messageHead_1347_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v_messageCount_1348_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_bodyBytesRead_1349_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_headerBytesRead_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*6, v_noMoreInput_1351_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1369_, lean_object* v_n_1370_, lean_object* v_reader_1371_){
_start:
{
uint8_t v_dir_boxed_1372_; lean_object* v_res_1373_; 
v_dir_boxed_1372_ = lean_unbox(v_dir_1369_);
v_res_1373_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1372_, v_n_1370_, v_reader_1371_);
lean_dec(v_n_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1376_){
_start:
{
lean_object* v_input_1377_; lean_object* v_messageHead_1378_; lean_object* v_messageCount_1379_; uint8_t v_noMoreInput_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1389_; 
v_input_1377_ = lean_ctor_get(v_reader_1376_, 1);
v_messageHead_1378_ = lean_ctor_get(v_reader_1376_, 2);
v_messageCount_1379_ = lean_ctor_get(v_reader_1376_, 3);
v_noMoreInput_1380_ = lean_ctor_get_uint8(v_reader_1376_, sizeof(void*)*6);
v_isSharedCheck_1389_ = !lean_is_exclusive(v_reader_1376_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; lean_object* v_unused_1392_; 
v_unused_1390_ = lean_ctor_get(v_reader_1376_, 5);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_reader_1376_, 4);
lean_dec(v_unused_1391_);
v_unused_1392_ = lean_ctor_get(v_reader_1376_, 0);
lean_dec(v_unused_1392_);
v___x_1382_ = v_reader_1376_;
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_messageCount_1379_);
lean_inc(v_messageHead_1378_);
lean_inc(v_input_1377_);
lean_dec(v_reader_1376_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1389_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 5, v___x_1384_);
lean_ctor_set(v___x_1382_, 4, v___x_1384_);
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_input_1377_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_messageHead_1378_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_messageCount_1379_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1388_, 5, v___x_1384_);
lean_ctor_set_uint8(v_reuseFailAlloc_1388_, sizeof(void*)*6, v_noMoreInput_1380_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1393_, lean_object* v_reader_1394_){
_start:
{
lean_object* v_input_1395_; lean_object* v_messageHead_1396_; lean_object* v_messageCount_1397_; uint8_t v_noMoreInput_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1407_; 
v_input_1395_ = lean_ctor_get(v_reader_1394_, 1);
v_messageHead_1396_ = lean_ctor_get(v_reader_1394_, 2);
v_messageCount_1397_ = lean_ctor_get(v_reader_1394_, 3);
v_noMoreInput_1398_ = lean_ctor_get_uint8(v_reader_1394_, sizeof(void*)*6);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_reader_1394_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; 
v_unused_1408_ = lean_ctor_get(v_reader_1394_, 5);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_reader_1394_, 4);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_reader_1394_, 0);
lean_dec(v_unused_1410_);
v___x_1400_ = v_reader_1394_;
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_messageCount_1397_);
lean_inc(v_messageHead_1396_);
lean_inc(v_input_1395_);
lean_dec(v_reader_1394_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 5, v___x_1402_);
lean_ctor_set(v___x_1400_, 4, v___x_1402_);
lean_ctor_set(v___x_1400_, 0, v___x_1403_);
v___x_1405_ = v___x_1400_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_input_1395_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_messageHead_1396_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_messageCount_1397_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1406_, 5, v___x_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*6, v_noMoreInput_1398_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1411_, lean_object* v_reader_1412_){
_start:
{
uint8_t v_dir_boxed_1413_; lean_object* v_res_1414_; 
v_dir_boxed_1413_ = lean_unbox(v_dir_1411_);
v_res_1414_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1413_, v_reader_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1415_, lean_object* v_reader_1416_){
_start:
{
lean_object* v_state_1417_; lean_object* v_input_1418_; lean_object* v_messageHead_1419_; lean_object* v_messageCount_1420_; lean_object* v_bodyBytesRead_1421_; lean_object* v_headerBytesRead_1422_; uint8_t v_noMoreInput_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
v_state_1417_ = lean_ctor_get(v_reader_1416_, 0);
v_input_1418_ = lean_ctor_get(v_reader_1416_, 1);
v_messageHead_1419_ = lean_ctor_get(v_reader_1416_, 2);
v_messageCount_1420_ = lean_ctor_get(v_reader_1416_, 3);
v_bodyBytesRead_1421_ = lean_ctor_get(v_reader_1416_, 4);
v_headerBytesRead_1422_ = lean_ctor_get(v_reader_1416_, 5);
v_noMoreInput_1423_ = lean_ctor_get_uint8(v_reader_1416_, sizeof(void*)*6);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_reader_1416_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1425_ = v_reader_1416_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_headerBytesRead_1422_);
lean_inc(v_bodyBytesRead_1421_);
lean_inc(v_messageCount_1420_);
lean_inc(v_messageHead_1419_);
lean_inc(v_input_1418_);
lean_inc(v_state_1417_);
lean_dec(v_reader_1416_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_nat_add(v_bodyBytesRead_1421_, v_n_1415_);
lean_dec(v_bodyBytesRead_1421_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 4, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_state_1417_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_input_1418_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_messageHead_1419_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_messageCount_1420_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 5, v_headerBytesRead_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1430_, sizeof(void*)*6, v_noMoreInput_1423_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1432_, lean_object* v_reader_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1432_, v_reader_1433_);
lean_dec(v_n_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1435_, lean_object* v_n_1436_, lean_object* v_reader_1437_){
_start:
{
lean_object* v_state_1438_; lean_object* v_input_1439_; lean_object* v_messageHead_1440_; lean_object* v_messageCount_1441_; lean_object* v_bodyBytesRead_1442_; lean_object* v_headerBytesRead_1443_; uint8_t v_noMoreInput_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1452_; 
v_state_1438_ = lean_ctor_get(v_reader_1437_, 0);
v_input_1439_ = lean_ctor_get(v_reader_1437_, 1);
v_messageHead_1440_ = lean_ctor_get(v_reader_1437_, 2);
v_messageCount_1441_ = lean_ctor_get(v_reader_1437_, 3);
v_bodyBytesRead_1442_ = lean_ctor_get(v_reader_1437_, 4);
v_headerBytesRead_1443_ = lean_ctor_get(v_reader_1437_, 5);
v_noMoreInput_1444_ = lean_ctor_get_uint8(v_reader_1437_, sizeof(void*)*6);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_reader_1437_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1446_ = v_reader_1437_;
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_headerBytesRead_1443_);
lean_inc(v_bodyBytesRead_1442_);
lean_inc(v_messageCount_1441_);
lean_inc(v_messageHead_1440_);
lean_inc(v_input_1439_);
lean_inc(v_state_1438_);
lean_dec(v_reader_1437_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1452_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1448_ = lean_nat_add(v_bodyBytesRead_1442_, v_n_1436_);
lean_dec(v_bodyBytesRead_1442_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 4, v___x_1448_);
v___x_1450_ = v___x_1446_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_state_1438_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_input_1439_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_messageHead_1440_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_messageCount_1441_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1451_, 5, v_headerBytesRead_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1451_, sizeof(void*)*6, v_noMoreInput_1444_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1453_, lean_object* v_n_1454_, lean_object* v_reader_1455_){
_start:
{
uint8_t v_dir_boxed_1456_; lean_object* v_res_1457_; 
v_dir_boxed_1456_ = lean_unbox(v_dir_1453_);
v_res_1457_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1456_, v_n_1454_, v_reader_1455_);
lean_dec(v_n_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1458_, lean_object* v_reader_1459_){
_start:
{
lean_object* v_state_1460_; lean_object* v_input_1461_; lean_object* v_messageHead_1462_; lean_object* v_messageCount_1463_; lean_object* v_bodyBytesRead_1464_; lean_object* v_headerBytesRead_1465_; uint8_t v_noMoreInput_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_state_1460_ = lean_ctor_get(v_reader_1459_, 0);
v_input_1461_ = lean_ctor_get(v_reader_1459_, 1);
v_messageHead_1462_ = lean_ctor_get(v_reader_1459_, 2);
v_messageCount_1463_ = lean_ctor_get(v_reader_1459_, 3);
v_bodyBytesRead_1464_ = lean_ctor_get(v_reader_1459_, 4);
v_headerBytesRead_1465_ = lean_ctor_get(v_reader_1459_, 5);
v_noMoreInput_1466_ = lean_ctor_get_uint8(v_reader_1459_, sizeof(void*)*6);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_reader_1459_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1468_ = v_reader_1459_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_headerBytesRead_1465_);
lean_inc(v_bodyBytesRead_1464_);
lean_inc(v_messageCount_1463_);
lean_inc(v_messageHead_1462_);
lean_inc(v_input_1461_);
lean_inc(v_state_1460_);
lean_dec(v_reader_1459_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_nat_add(v_headerBytesRead_1465_, v_n_1458_);
lean_dec(v_headerBytesRead_1465_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 5, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_state_1460_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_input_1461_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_messageHead_1462_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_messageCount_1463_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_bodyBytesRead_1464_);
lean_ctor_set(v_reuseFailAlloc_1473_, 5, v___x_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*6, v_noMoreInput_1466_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1475_, lean_object* v_reader_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1475_, v_reader_1476_);
lean_dec(v_n_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1478_, lean_object* v_n_1479_, lean_object* v_reader_1480_){
_start:
{
lean_object* v_state_1481_; lean_object* v_input_1482_; lean_object* v_messageHead_1483_; lean_object* v_messageCount_1484_; lean_object* v_bodyBytesRead_1485_; lean_object* v_headerBytesRead_1486_; uint8_t v_noMoreInput_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_state_1481_ = lean_ctor_get(v_reader_1480_, 0);
v_input_1482_ = lean_ctor_get(v_reader_1480_, 1);
v_messageHead_1483_ = lean_ctor_get(v_reader_1480_, 2);
v_messageCount_1484_ = lean_ctor_get(v_reader_1480_, 3);
v_bodyBytesRead_1485_ = lean_ctor_get(v_reader_1480_, 4);
v_headerBytesRead_1486_ = lean_ctor_get(v_reader_1480_, 5);
v_noMoreInput_1487_ = lean_ctor_get_uint8(v_reader_1480_, sizeof(void*)*6);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_reader_1480_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1489_ = v_reader_1480_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_headerBytesRead_1486_);
lean_inc(v_bodyBytesRead_1485_);
lean_inc(v_messageCount_1484_);
lean_inc(v_messageHead_1483_);
lean_inc(v_input_1482_);
lean_inc(v_state_1481_);
lean_dec(v_reader_1480_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_nat_add(v_headerBytesRead_1486_, v_n_1479_);
lean_dec(v_headerBytesRead_1486_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 5, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_state_1481_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v_input_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_messageHead_1483_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_messageCount_1484_);
lean_ctor_set(v_reuseFailAlloc_1494_, 4, v_bodyBytesRead_1485_);
lean_ctor_set(v_reuseFailAlloc_1494_, 5, v___x_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1494_, sizeof(void*)*6, v_noMoreInput_1487_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1496_, lean_object* v_n_1497_, lean_object* v_reader_1498_){
_start:
{
uint8_t v_dir_boxed_1499_; lean_object* v_res_1500_; 
v_dir_boxed_1499_ = lean_unbox(v_dir_1496_);
v_res_1500_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1499_, v_n_1497_, v_reader_1498_);
lean_dec(v_n_1497_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1501_, lean_object* v_reader_1502_){
_start:
{
lean_object* v_input_1503_; lean_object* v_messageHead_1504_; lean_object* v_messageCount_1505_; lean_object* v_bodyBytesRead_1506_; lean_object* v_headerBytesRead_1507_; uint8_t v_noMoreInput_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
v_input_1503_ = lean_ctor_get(v_reader_1502_, 1);
v_messageHead_1504_ = lean_ctor_get(v_reader_1502_, 2);
v_messageCount_1505_ = lean_ctor_get(v_reader_1502_, 3);
v_bodyBytesRead_1506_ = lean_ctor_get(v_reader_1502_, 4);
v_headerBytesRead_1507_ = lean_ctor_get(v_reader_1502_, 5);
v_noMoreInput_1508_ = lean_ctor_get_uint8(v_reader_1502_, sizeof(void*)*6);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_reader_1502_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_reader_1502_, 0);
lean_dec(v_unused_1518_);
v___x_1510_ = v_reader_1502_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_headerBytesRead_1507_);
lean_inc(v_bodyBytesRead_1506_);
lean_inc(v_messageCount_1505_);
lean_inc(v_messageHead_1504_);
lean_inc(v_input_1503_);
lean_dec(v_reader_1502_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_size_1501_);
v___x_1513_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_input_1503_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_messageHead_1504_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_messageCount_1505_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_bodyBytesRead_1506_);
lean_ctor_set(v_reuseFailAlloc_1516_, 5, v_headerBytesRead_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1516_, sizeof(void*)*6, v_noMoreInput_1508_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1519_, lean_object* v_size_1520_, lean_object* v_reader_1521_){
_start:
{
lean_object* v_input_1522_; lean_object* v_messageHead_1523_; lean_object* v_messageCount_1524_; lean_object* v_bodyBytesRead_1525_; lean_object* v_headerBytesRead_1526_; uint8_t v_noMoreInput_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1536_; 
v_input_1522_ = lean_ctor_get(v_reader_1521_, 1);
v_messageHead_1523_ = lean_ctor_get(v_reader_1521_, 2);
v_messageCount_1524_ = lean_ctor_get(v_reader_1521_, 3);
v_bodyBytesRead_1525_ = lean_ctor_get(v_reader_1521_, 4);
v_headerBytesRead_1526_ = lean_ctor_get(v_reader_1521_, 5);
v_noMoreInput_1527_ = lean_ctor_get_uint8(v_reader_1521_, sizeof(void*)*6);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_reader_1521_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_reader_1521_, 0);
lean_dec(v_unused_1537_);
v___x_1529_ = v_reader_1521_;
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_headerBytesRead_1526_);
lean_inc(v_bodyBytesRead_1525_);
lean_inc(v_messageCount_1524_);
lean_inc(v_messageHead_1523_);
lean_inc(v_input_1522_);
lean_dec(v_reader_1521_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_size_1520_);
v___x_1532_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_input_1522_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_messageHead_1523_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_messageCount_1524_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v_bodyBytesRead_1525_);
lean_ctor_set(v_reuseFailAlloc_1535_, 5, v_headerBytesRead_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1535_, sizeof(void*)*6, v_noMoreInput_1527_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1538_, lean_object* v_size_1539_, lean_object* v_reader_1540_){
_start:
{
uint8_t v_dir_boxed_1541_; lean_object* v_res_1542_; 
v_dir_boxed_1541_ = lean_unbox(v_dir_1538_);
v_res_1542_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1541_, v_size_1539_, v_reader_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1545_){
_start:
{
lean_object* v_input_1546_; lean_object* v_messageHead_1547_; lean_object* v_messageCount_1548_; lean_object* v_bodyBytesRead_1549_; lean_object* v_headerBytesRead_1550_; uint8_t v_noMoreInput_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1559_; 
v_input_1546_ = lean_ctor_get(v_reader_1545_, 1);
v_messageHead_1547_ = lean_ctor_get(v_reader_1545_, 2);
v_messageCount_1548_ = lean_ctor_get(v_reader_1545_, 3);
v_bodyBytesRead_1549_ = lean_ctor_get(v_reader_1545_, 4);
v_headerBytesRead_1550_ = lean_ctor_get(v_reader_1545_, 5);
v_noMoreInput_1551_ = lean_ctor_get_uint8(v_reader_1545_, sizeof(void*)*6);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_reader_1545_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_reader_1545_, 0);
lean_dec(v_unused_1560_);
v___x_1553_ = v_reader_1545_;
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_headerBytesRead_1550_);
lean_inc(v_bodyBytesRead_1549_);
lean_inc(v_messageCount_1548_);
lean_inc(v_messageHead_1547_);
lean_inc(v_input_1546_);
lean_dec(v_reader_1545_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1559_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1555_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1555_);
v___x_1557_ = v___x_1553_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_input_1546_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_messageHead_1547_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_messageCount_1548_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v_bodyBytesRead_1549_);
lean_ctor_set(v_reuseFailAlloc_1558_, 5, v_headerBytesRead_1550_);
lean_ctor_set_uint8(v_reuseFailAlloc_1558_, sizeof(void*)*6, v_noMoreInput_1551_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1561_, lean_object* v_reader_1562_){
_start:
{
lean_object* v_input_1563_; lean_object* v_messageHead_1564_; lean_object* v_messageCount_1565_; lean_object* v_bodyBytesRead_1566_; lean_object* v_headerBytesRead_1567_; uint8_t v_noMoreInput_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
v_input_1563_ = lean_ctor_get(v_reader_1562_, 1);
v_messageHead_1564_ = lean_ctor_get(v_reader_1562_, 2);
v_messageCount_1565_ = lean_ctor_get(v_reader_1562_, 3);
v_bodyBytesRead_1566_ = lean_ctor_get(v_reader_1562_, 4);
v_headerBytesRead_1567_ = lean_ctor_get(v_reader_1562_, 5);
v_noMoreInput_1568_ = lean_ctor_get_uint8(v_reader_1562_, sizeof(void*)*6);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_reader_1562_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_reader_1562_, 0);
lean_dec(v_unused_1577_);
v___x_1570_ = v_reader_1562_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_headerBytesRead_1567_);
lean_inc(v_bodyBytesRead_1566_);
lean_inc(v_messageCount_1565_);
lean_inc(v_messageHead_1564_);
lean_inc(v_input_1563_);
lean_dec(v_reader_1562_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_input_1563_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_messageHead_1564_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_messageCount_1565_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_bodyBytesRead_1566_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v_headerBytesRead_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1575_, sizeof(void*)*6, v_noMoreInput_1568_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1578_, lean_object* v_reader_1579_){
_start:
{
uint8_t v_dir_boxed_1580_; lean_object* v_res_1581_; 
v_dir_boxed_1580_ = lean_unbox(v_dir_1578_);
v_res_1581_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1580_, v_reader_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object* v_reader_1582_){
_start:
{
lean_object* v_state_1583_; lean_object* v_input_1584_; lean_object* v_messageHead_1585_; lean_object* v_messageCount_1586_; lean_object* v_bodyBytesRead_1587_; lean_object* v_headerBytesRead_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1596_; 
v_state_1583_ = lean_ctor_get(v_reader_1582_, 0);
v_input_1584_ = lean_ctor_get(v_reader_1582_, 1);
v_messageHead_1585_ = lean_ctor_get(v_reader_1582_, 2);
v_messageCount_1586_ = lean_ctor_get(v_reader_1582_, 3);
v_bodyBytesRead_1587_ = lean_ctor_get(v_reader_1582_, 4);
v_headerBytesRead_1588_ = lean_ctor_get(v_reader_1582_, 5);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_reader_1582_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1590_ = v_reader_1582_;
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_headerBytesRead_1588_);
lean_inc(v_bodyBytesRead_1587_);
lean_inc(v_messageCount_1586_);
lean_inc(v_messageHead_1585_);
lean_inc(v_input_1584_);
lean_inc(v_state_1583_);
lean_dec(v_reader_1582_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1596_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
uint8_t v___x_1592_; lean_object* v___x_1594_; 
v___x_1592_ = 1;
if (v_isShared_1591_ == 0)
{
v___x_1594_ = v___x_1590_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_state_1583_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_input_1584_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_messageHead_1585_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_messageCount_1586_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_bodyBytesRead_1587_);
lean_ctor_set(v_reuseFailAlloc_1595_, 5, v_headerBytesRead_1588_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_ctor_set_uint8(v___x_1594_, sizeof(void*)*6, v___x_1592_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t v_dir_1597_, lean_object* v_reader_1598_){
_start:
{
lean_object* v_state_1599_; lean_object* v_input_1600_; lean_object* v_messageHead_1601_; lean_object* v_messageCount_1602_; lean_object* v_bodyBytesRead_1603_; lean_object* v_headerBytesRead_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1612_; 
v_state_1599_ = lean_ctor_get(v_reader_1598_, 0);
v_input_1600_ = lean_ctor_get(v_reader_1598_, 1);
v_messageHead_1601_ = lean_ctor_get(v_reader_1598_, 2);
v_messageCount_1602_ = lean_ctor_get(v_reader_1598_, 3);
v_bodyBytesRead_1603_ = lean_ctor_get(v_reader_1598_, 4);
v_headerBytesRead_1604_ = lean_ctor_get(v_reader_1598_, 5);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_reader_1598_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1606_ = v_reader_1598_;
v_isShared_1607_ = v_isSharedCheck_1612_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_headerBytesRead_1604_);
lean_inc(v_bodyBytesRead_1603_);
lean_inc(v_messageCount_1602_);
lean_inc(v_messageHead_1601_);
lean_inc(v_input_1600_);
lean_inc(v_state_1599_);
lean_dec(v_reader_1598_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1612_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
uint8_t v___x_1608_; lean_object* v___x_1610_; 
v___x_1608_ = 1;
if (v_isShared_1607_ == 0)
{
v___x_1610_ = v___x_1606_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_state_1599_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_input_1600_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_messageHead_1601_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_messageCount_1602_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_bodyBytesRead_1603_);
lean_ctor_set(v_reuseFailAlloc_1611_, 5, v_headerBytesRead_1604_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_ctor_set_uint8(v___x_1610_, sizeof(void*)*6, v___x_1608_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object* v_dir_1613_, lean_object* v_reader_1614_){
_start:
{
uint8_t v_dir_boxed_1615_; lean_object* v_res_1616_; 
v_dir_boxed_1615_ = lean_unbox(v_dir_1613_);
v_res_1616_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_1615_, v_reader_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1617_, lean_object* v_reader_1618_){
_start:
{
lean_object* v_messageHead_1619_; uint8_t v___x_1620_; 
v_messageHead_1619_ = lean_ctor_get(v_reader_1618_, 2);
v___x_1620_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1617_, v_messageHead_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1621_, lean_object* v_reader_1622_){
_start:
{
uint8_t v_dir_boxed_1623_; uint8_t v_res_1624_; lean_object* v_r_1625_; 
v_dir_boxed_1623_ = lean_unbox(v_dir_1621_);
v_res_1624_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1623_, v_reader_1622_);
lean_dec_ref(v_reader_1622_);
v_r_1625_ = lean_box(v_res_1624_);
return v_r_1625_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Reader(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Protocol_H1_Reader(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Http_Internal(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Protocol_H1_Reader(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Internal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1_Reader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Protocol_H1_Reader(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Protocol_H1_Reader(builtin);
}
#ifdef __cplusplus
}
#endif
