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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_t_8_, 1);
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
lean_dec_ref_known(v_t_8_, 2);
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
lean_dec_ref_known(v_x_69_, 1);
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
lean_dec_ref_known(v_x_94_, 2);
return v_head_98_;
}
else
{
lean_object* v_head_99_; lean_object* v___x_100_; 
lean_inc(v_tail_97_);
v_head_99_ = lean_ctor_get(v_x_94_, 0);
lean_inc(v_head_99_);
lean_dec_ref_known(v_x_94_, 2);
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
lean_dec_ref_known(v_x_173_, 2);
v___x_178_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_177_);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v_tail_176_);
v_head_179_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_179_);
lean_dec_ref_known(v_x_173_, 2);
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
lean_dec_ref_known(v_t_408_, 1);
v___x_411_ = lean_apply_1(v_k_409_, v_a_410_);
return v___x_411_;
}
case 2:
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v_t_408_, 1);
v___x_413_ = lean_apply_1(v_k_409_, v_a_412_);
return v___x_413_;
}
case 3:
{
lean_object* v_a_414_; lean_object* v___x_415_; 
v_a_414_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v_t_408_, 1);
v___x_415_ = lean_apply_1(v_k_409_, v_a_414_);
return v___x_415_;
}
case 7:
{
lean_object* v_error_416_; lean_object* v___x_417_; 
v_error_416_ = lean_ctor_get(v_t_408_, 0);
lean_inc(v_error_416_);
lean_dec_ref_known(v_t_408_, 1);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg(){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object* v___dummy_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_567_){
_start:
{
uint8_t v_dir_boxed_568_; lean_object* v_res_569_; 
v_dir_boxed_568_ = lean_unbox(v_dir_567_);
v_res_569_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg(){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object* v___dummy_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_box(0);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_576_){
_start:
{
uint8_t v_a_11__boxed_577_; lean_object* v_res_578_; 
v_a_11__boxed_577_ = lean_unbox(v_a_576_);
v_res_578_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_11__boxed_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_615_, lean_object* v_prec_616_){
_start:
{
lean_object* v___y_618_; lean_object* v___y_625_; lean_object* v___y_632_; lean_object* v___y_639_; 
switch(lean_obj_tag(v_x_615_))
{
case 0:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(1024u);
v___x_646_ = lean_nat_dec_le(v___x_645_, v_prec_616_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_639_ = v___x_647_;
goto v___jp_638_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_639_ = v___x_648_;
goto v___jp_638_;
}
}
case 1:
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_669_; 
v_a_649_ = lean_ctor_get(v_x_615_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_669_ == 0)
{
v___x_651_ = v_x_615_;
v_isShared_652_ = v_isSharedCheck_669_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v_x_615_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_669_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___y_654_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(1024u);
v___x_666_ = lean_nat_dec_le(v___x_665_, v_prec_616_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_654_ = v___x_667_;
goto v___jp_653_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_654_ = v___x_668_;
goto v___jp_653_;
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_656_ = l_Nat_reprFast(v_a_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set_tag(v___x_651_, 3);
lean_ctor_set(v___x_651_, 0, v___x_656_);
v___x_658_ = v___x_651_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_664_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_659_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_655_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_inc(v___y_654_);
v___x_660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_660_, 0, v___y_654_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = 0;
v___x_662_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*1, v___x_661_);
v___x_663_ = l_Repr_addAppParen(v___x_662_, v_prec_616_);
return v___x_663_;
}
}
}
}
case 2:
{
lean_object* v_a_670_; lean_object* v___y_672_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_a_670_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v_x_615_, 1);
v___x_681_ = lean_unsigned_to_nat(1024u);
v___x_682_ = lean_nat_dec_le(v___x_681_, v_prec_616_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
v___x_683_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_672_ = v___x_683_;
goto v___jp_671_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_672_ = v___x_684_;
goto v___jp_671_;
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_673_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_674_ = lean_unsigned_to_nat(1024u);
v___x_675_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_670_, v___x_674_);
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
lean_inc(v___y_672_);
v___x_677_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_677_, 0, v___y_672_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = 0;
v___x_679_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*1, v___x_678_);
v___x_680_ = l_Repr_addAppParen(v___x_679_, v_prec_616_);
return v___x_680_;
}
}
case 3:
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___y_688_; uint8_t v___x_696_; 
v_a_685_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v_x_615_, 1);
v___x_686_ = lean_unsigned_to_nat(1024u);
v___x_696_ = lean_nat_dec_le(v___x_686_, v_prec_616_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_688_ = v___x_697_;
goto v___jp_687_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_688_ = v___x_698_;
goto v___jp_687_;
}
v___jp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_689_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_690_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_685_, v___x_686_);
v___x_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
lean_inc(v___y_688_);
v___x_692_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_692_, 0, v___y_688_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = 0;
v___x_694_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*1, v___x_693_);
v___x_695_ = l_Repr_addAppParen(v___x_694_, v_prec_616_);
return v___x_695_;
}
}
case 4:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(1024u);
v___x_700_ = lean_nat_dec_le(v___x_699_, v_prec_616_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_632_ = v___x_701_;
goto v___jp_631_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_632_ = v___x_702_;
goto v___jp_631_;
}
}
case 5:
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(1024u);
v___x_704_ = lean_nat_dec_le(v___x_703_, v_prec_616_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_625_ = v___x_705_;
goto v___jp_624_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_625_ = v___x_706_;
goto v___jp_624_;
}
}
case 6:
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(1024u);
v___x_708_ = lean_nat_dec_le(v___x_707_, v_prec_616_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_618_ = v___x_709_;
goto v___jp_617_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_618_ = v___x_710_;
goto v___jp_617_;
}
}
default: 
{
lean_object* v_error_711_; lean_object* v___y_713_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_error_711_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_error_711_);
lean_dec_ref_known(v_x_615_, 1);
v___x_722_ = lean_unsigned_to_nat(1024u);
v___x_723_ = lean_nat_dec_le(v___x_722_, v_prec_616_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_713_ = v___x_724_;
goto v___jp_712_;
}
else
{
lean_object* v___x_725_; 
v___x_725_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_713_ = v___x_725_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_714_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19));
v___x_715_ = lean_unsigned_to_nat(1024u);
v___x_716_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_711_, v___x_715_);
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_714_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
lean_inc(v___y_713_);
v___x_718_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_718_, 0, v___y_713_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = 0;
v___x_720_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set_uint8(v___x_720_, sizeof(void*)*1, v___x_719_);
v___x_721_ = l_Repr_addAppParen(v___x_720_, v_prec_616_);
return v___x_721_;
}
}
}
v___jp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_619_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_618_);
v___x_620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_620_, 0, v___y_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = 0;
v___x_622_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v___x_621_);
v___x_623_ = l_Repr_addAppParen(v___x_622_, v_prec_616_);
return v___x_623_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_626_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_625_);
v___x_627_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_627_, 0, v___y_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = 0;
v___x_629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set_uint8(v___x_629_, sizeof(void*)*1, v___x_628_);
v___x_630_ = l_Repr_addAppParen(v___x_629_, v_prec_616_);
return v___x_630_;
}
v___jp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_633_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_632_);
v___x_634_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_634_, 0, v___y_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = 0;
v___x_636_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set_uint8(v___x_636_, sizeof(void*)*1, v___x_635_);
v___x_637_ = l_Repr_addAppParen(v___x_636_, v_prec_616_);
return v___x_637_;
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_640_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_639_);
v___x_641_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_641_, 0, v___y_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = 0;
v___x_643_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*1, v___x_642_);
v___x_644_ = l_Repr_addAppParen(v___x_643_, v_prec_616_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_726_, lean_object* v_prec_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_726_, v_prec_727_);
lean_dec(v_prec_727_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_729_, lean_object* v_x_730_, lean_object* v_prec_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_730_, v_prec_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_733_, lean_object* v_x_734_, lean_object* v_prec_735_){
_start:
{
uint8_t v_dir_876__boxed_736_; lean_object* v_res_737_; 
v_dir_876__boxed_736_ = lean_unbox(v_dir_733_);
v_res_737_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_876__boxed_736_, v_x_734_, v_prec_735_);
lean_dec(v_prec_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_box(v_dir_738_);
v___x_740_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_741_){
_start:
{
uint8_t v_dir_5__boxed_742_; lean_object* v_res_743_; 
v_dir_5__boxed_742_ = lean_unbox(v_dir_741_);
v_res_743_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_742_);
return v_res_743_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
switch(lean_obj_tag(v_x_744_))
{
case 0:
{
if (lean_obj_tag(v_x_745_) == 0)
{
uint8_t v___x_746_; 
v___x_746_ = 1;
return v___x_746_;
}
else
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
case 1:
{
if (lean_obj_tag(v_x_745_) == 1)
{
lean_object* v_a_748_; lean_object* v_a_749_; uint8_t v___x_750_; 
v_a_748_ = lean_ctor_get(v_x_744_, 0);
v_a_749_ = lean_ctor_get(v_x_745_, 0);
v___x_750_ = lean_nat_dec_eq(v_a_748_, v_a_749_);
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
}
case 2:
{
if (lean_obj_tag(v_x_745_) == 2)
{
lean_object* v_a_752_; lean_object* v_a_753_; uint8_t v___x_754_; 
v_a_752_ = lean_ctor_get(v_x_744_, 0);
v_a_753_ = lean_ctor_get(v_x_745_, 0);
v___x_754_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_752_, v_a_753_);
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
case 3:
{
if (lean_obj_tag(v_x_745_) == 3)
{
lean_object* v_a_756_; lean_object* v_a_757_; 
v_a_756_ = lean_ctor_get(v_x_744_, 0);
v_a_757_ = lean_ctor_get(v_x_745_, 0);
v_x_744_ = v_a_756_;
v_x_745_ = v_a_757_;
goto _start;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
case 4:
{
if (lean_obj_tag(v_x_745_) == 4)
{
uint8_t v___x_760_; 
v___x_760_ = 1;
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
case 5:
{
if (lean_obj_tag(v_x_745_) == 5)
{
uint8_t v___x_762_; 
v___x_762_ = 1;
return v___x_762_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
case 6:
{
if (lean_obj_tag(v_x_745_) == 6)
{
uint8_t v___x_764_; 
v___x_764_ = 1;
return v___x_764_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = 0;
return v___x_765_;
}
}
default: 
{
if (lean_obj_tag(v_x_745_) == 7)
{
lean_object* v_error_766_; lean_object* v_error_767_; uint8_t v___x_768_; 
v_error_766_ = lean_ctor_get(v_x_744_, 0);
v_error_767_ = lean_ctor_get(v_x_745_, 0);
v___x_768_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_error_766_, v_error_767_);
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = 0;
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_770_, v_x_771_);
lean_dec(v_x_771_);
lean_dec(v_x_770_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
uint8_t v___x_777_; 
v___x_777_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
uint8_t v_dir_183__boxed_781_; uint8_t v_res_782_; lean_object* v_r_783_; 
v_dir_183__boxed_781_ = lean_unbox(v_dir_778_);
v_res_782_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_183__boxed_781_, v_x_779_, v_x_780_);
lean_dec(v_x_780_);
lean_dec(v_x_779_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(v_dir_784_);
v___x_786_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_787_){
_start:
{
uint8_t v_dir_5__boxed_788_; lean_object* v_res_789_; 
v_dir_5__boxed_788_ = lean_unbox(v_dir_787_);
v_res_789_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_788_);
return v_res_789_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_790_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_794_){
_start:
{
uint8_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_794_);
lean_dec_ref(v_reader_794_);
v_r_796_ = lean_box(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_797_, lean_object* v_reader_798_){
_start:
{
lean_object* v_state_799_; 
v_state_799_ = lean_ctor_get(v_reader_798_, 0);
if (lean_obj_tag(v_state_799_) == 6)
{
uint8_t v___x_800_; 
v___x_800_ = 1;
return v___x_800_;
}
else
{
uint8_t v___x_801_; 
v___x_801_ = 0;
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_802_, lean_object* v_reader_803_){
_start:
{
uint8_t v_dir_boxed_804_; uint8_t v_res_805_; lean_object* v_r_806_; 
v_dir_boxed_804_ = lean_unbox(v_dir_802_);
v_res_805_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_804_, v_reader_803_);
lean_dec_ref(v_reader_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_807_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_811_);
lean_dec_ref(v_reader_811_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_814_, lean_object* v_reader_815_){
_start:
{
lean_object* v_state_816_; 
v_state_816_ = lean_ctor_get(v_reader_815_, 0);
if (lean_obj_tag(v_state_816_) == 5)
{
uint8_t v___x_817_; 
v___x_817_ = 1;
return v___x_817_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_819_, lean_object* v_reader_820_){
_start:
{
uint8_t v_dir_boxed_821_; uint8_t v_res_822_; lean_object* v_r_823_; 
v_dir_boxed_821_ = lean_unbox(v_dir_819_);
v_res_822_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_821_, v_reader_820_);
lean_dec_ref(v_reader_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object* v_reader_824_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object* v_reader_828_){
_start:
{
uint8_t v_res_829_; lean_object* v_r_830_; 
v_res_829_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_828_);
lean_dec_ref(v_reader_828_);
v_r_830_ = lean_box(v_res_829_);
return v_r_830_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t v_dir_831_, lean_object* v_reader_832_){
_start:
{
lean_object* v_state_833_; 
v_state_833_ = lean_ctor_get(v_reader_832_, 0);
if (lean_obj_tag(v_state_833_) == 7)
{
uint8_t v___x_834_; 
v___x_834_ = 1;
return v___x_834_;
}
else
{
uint8_t v___x_835_; 
v___x_835_ = 0;
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object* v_dir_836_, lean_object* v_reader_837_){
_start:
{
uint8_t v_dir_boxed_838_; uint8_t v_res_839_; lean_object* v_r_840_; 
v_dir_boxed_838_ = lean_unbox(v_dir_836_);
v_res_839_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_838_, v_reader_837_);
lean_dec_ref(v_reader_837_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_841_, lean_object* v_reader_842_){
_start:
{
lean_object* v_input_843_; lean_object* v_state_844_; lean_object* v_messageHead_845_; lean_object* v_messageCount_846_; lean_object* v_bodyBytesRead_847_; lean_object* v_headerBytesRead_848_; uint8_t v_noMoreInput_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_870_; 
v_input_843_ = lean_ctor_get(v_reader_842_, 1);
v_state_844_ = lean_ctor_get(v_reader_842_, 0);
v_messageHead_845_ = lean_ctor_get(v_reader_842_, 2);
v_messageCount_846_ = lean_ctor_get(v_reader_842_, 3);
v_bodyBytesRead_847_ = lean_ctor_get(v_reader_842_, 4);
v_headerBytesRead_848_ = lean_ctor_get(v_reader_842_, 5);
v_noMoreInput_849_ = lean_ctor_get_uint8(v_reader_842_, sizeof(void*)*6);
v_isSharedCheck_870_ = !lean_is_exclusive(v_reader_842_);
if (v_isSharedCheck_870_ == 0)
{
v___x_851_ = v_reader_842_;
v_isShared_852_ = v_isSharedCheck_870_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_headerBytesRead_848_);
lean_inc(v_bodyBytesRead_847_);
lean_inc(v_messageCount_846_);
lean_inc(v_messageHead_845_);
lean_inc(v_input_843_);
lean_inc(v_state_844_);
lean_dec(v_reader_842_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_870_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_array_853_; lean_object* v_idx_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_array_853_ = lean_ctor_get(v_input_843_, 0);
lean_inc_ref(v_array_853_);
v_idx_854_ = lean_ctor_get(v_input_843_, 1);
lean_inc(v_idx_854_);
lean_dec_ref(v_input_843_);
v___x_855_ = lean_byte_array_size(v_array_853_);
v___x_856_ = lean_nat_dec_le(v___x_855_, v_idx_854_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_857_ = l_ByteArray_extract(v_array_853_, v_idx_854_, v___x_855_);
lean_dec_ref(v_array_853_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_byte_array_size(v___x_857_);
v___x_860_ = lean_byte_array_size(v_data_841_);
v___x_861_ = lean_byte_array_copy_slice(v_data_841_, v___x_858_, v___x_857_, v___x_859_, v___x_860_, v___x_856_);
lean_dec_ref(v_data_841_);
v___x_862_ = l_ByteArray_mkIterator(v___x_861_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_862_);
v___x_864_ = v___x_851_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_state_844_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_messageHead_845_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_messageCount_846_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_bodyBytesRead_847_);
lean_ctor_set(v_reuseFailAlloc_865_, 5, v_headerBytesRead_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_865_, sizeof(void*)*6, v_noMoreInput_849_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec(v_idx_854_);
lean_dec_ref(v_array_853_);
v___x_866_ = l_ByteArray_mkIterator(v_data_841_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_866_);
v___x_868_ = v___x_851_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_state_844_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_messageHead_845_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_messageCount_846_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_bodyBytesRead_847_);
lean_ctor_set(v_reuseFailAlloc_869_, 5, v_headerBytesRead_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_869_, sizeof(void*)*6, v_noMoreInput_849_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_871_, lean_object* v_data_872_, lean_object* v_reader_873_){
_start:
{
lean_object* v_input_874_; lean_object* v_state_875_; lean_object* v_messageHead_876_; lean_object* v_messageCount_877_; lean_object* v_bodyBytesRead_878_; lean_object* v_headerBytesRead_879_; uint8_t v_noMoreInput_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_901_; 
v_input_874_ = lean_ctor_get(v_reader_873_, 1);
v_state_875_ = lean_ctor_get(v_reader_873_, 0);
v_messageHead_876_ = lean_ctor_get(v_reader_873_, 2);
v_messageCount_877_ = lean_ctor_get(v_reader_873_, 3);
v_bodyBytesRead_878_ = lean_ctor_get(v_reader_873_, 4);
v_headerBytesRead_879_ = lean_ctor_get(v_reader_873_, 5);
v_noMoreInput_880_ = lean_ctor_get_uint8(v_reader_873_, sizeof(void*)*6);
v_isSharedCheck_901_ = !lean_is_exclusive(v_reader_873_);
if (v_isSharedCheck_901_ == 0)
{
v___x_882_ = v_reader_873_;
v_isShared_883_ = v_isSharedCheck_901_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_headerBytesRead_879_);
lean_inc(v_bodyBytesRead_878_);
lean_inc(v_messageCount_877_);
lean_inc(v_messageHead_876_);
lean_inc(v_input_874_);
lean_inc(v_state_875_);
lean_dec(v_reader_873_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_901_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_array_884_; lean_object* v_idx_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_array_884_ = lean_ctor_get(v_input_874_, 0);
lean_inc_ref(v_array_884_);
v_idx_885_ = lean_ctor_get(v_input_874_, 1);
lean_inc(v_idx_885_);
lean_dec_ref(v_input_874_);
v___x_886_ = lean_byte_array_size(v_array_884_);
v___x_887_ = lean_nat_dec_le(v___x_886_, v_idx_885_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_888_ = l_ByteArray_extract(v_array_884_, v_idx_885_, v___x_886_);
lean_dec_ref(v_array_884_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_byte_array_size(v___x_888_);
v___x_891_ = lean_byte_array_size(v_data_872_);
v___x_892_ = lean_byte_array_copy_slice(v_data_872_, v___x_889_, v___x_888_, v___x_890_, v___x_891_, v___x_887_);
lean_dec_ref(v_data_872_);
v___x_893_ = l_ByteArray_mkIterator(v___x_892_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_893_);
v___x_895_ = v___x_882_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_state_875_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_messageHead_876_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_messageCount_877_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_bodyBytesRead_878_);
lean_ctor_set(v_reuseFailAlloc_896_, 5, v_headerBytesRead_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_896_, sizeof(void*)*6, v_noMoreInput_880_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_idx_885_);
lean_dec_ref(v_array_884_);
v___x_897_ = l_ByteArray_mkIterator(v_data_872_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_897_);
v___x_899_ = v___x_882_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_state_875_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_messageHead_876_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_messageCount_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v_bodyBytesRead_878_);
lean_ctor_set(v_reuseFailAlloc_900_, 5, v_headerBytesRead_879_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*6, v_noMoreInput_880_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_902_, lean_object* v_data_903_, lean_object* v_reader_904_){
_start:
{
uint8_t v_dir_boxed_905_; lean_object* v_res_906_; 
v_dir_boxed_905_ = lean_unbox(v_dir_902_);
v_res_906_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_905_, v_data_903_, v_reader_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_907_, lean_object* v_reader_908_){
_start:
{
lean_object* v_state_909_; lean_object* v_messageHead_910_; lean_object* v_messageCount_911_; lean_object* v_bodyBytesRead_912_; lean_object* v_headerBytesRead_913_; uint8_t v_noMoreInput_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_state_909_ = lean_ctor_get(v_reader_908_, 0);
v_messageHead_910_ = lean_ctor_get(v_reader_908_, 2);
v_messageCount_911_ = lean_ctor_get(v_reader_908_, 3);
v_bodyBytesRead_912_ = lean_ctor_get(v_reader_908_, 4);
v_headerBytesRead_913_ = lean_ctor_get(v_reader_908_, 5);
v_noMoreInput_914_ = lean_ctor_get_uint8(v_reader_908_, sizeof(void*)*6);
v_isSharedCheck_921_ = !lean_is_exclusive(v_reader_908_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_reader_908_, 1);
lean_dec(v_unused_922_);
v___x_916_ = v_reader_908_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_headerBytesRead_913_);
lean_inc(v_bodyBytesRead_912_);
lean_inc(v_messageCount_911_);
lean_inc(v_messageHead_910_);
lean_inc(v_state_909_);
lean_dec(v_reader_908_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v_input_907_);
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_state_909_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_input_907_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_messageHead_910_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_messageCount_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_bodyBytesRead_912_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_headerBytesRead_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_920_, sizeof(void*)*6, v_noMoreInput_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_923_, lean_object* v_input_924_, lean_object* v_reader_925_){
_start:
{
lean_object* v_state_926_; lean_object* v_messageHead_927_; lean_object* v_messageCount_928_; lean_object* v_bodyBytesRead_929_; lean_object* v_headerBytesRead_930_; uint8_t v_noMoreInput_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_state_926_ = lean_ctor_get(v_reader_925_, 0);
v_messageHead_927_ = lean_ctor_get(v_reader_925_, 2);
v_messageCount_928_ = lean_ctor_get(v_reader_925_, 3);
v_bodyBytesRead_929_ = lean_ctor_get(v_reader_925_, 4);
v_headerBytesRead_930_ = lean_ctor_get(v_reader_925_, 5);
v_noMoreInput_931_ = lean_ctor_get_uint8(v_reader_925_, sizeof(void*)*6);
v_isSharedCheck_938_ = !lean_is_exclusive(v_reader_925_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_reader_925_, 1);
lean_dec(v_unused_939_);
v___x_933_ = v_reader_925_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_headerBytesRead_930_);
lean_inc(v_bodyBytesRead_929_);
lean_inc(v_messageCount_928_);
lean_inc(v_messageHead_927_);
lean_inc(v_state_926_);
lean_dec(v_reader_925_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v_input_924_);
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_state_926_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_input_924_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_messageHead_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_messageCount_928_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_bodyBytesRead_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 5, v_headerBytesRead_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*6, v_noMoreInput_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object* v_dir_940_, lean_object* v_input_941_, lean_object* v_reader_942_){
_start:
{
uint8_t v_dir_boxed_943_; lean_object* v_res_944_; 
v_dir_boxed_943_ = lean_unbox(v_dir_940_);
v_res_944_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_943_, v_input_941_, v_reader_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object* v_messageHead_945_, lean_object* v_reader_946_){
_start:
{
lean_object* v_state_947_; lean_object* v_input_948_; lean_object* v_messageCount_949_; lean_object* v_bodyBytesRead_950_; lean_object* v_headerBytesRead_951_; uint8_t v_noMoreInput_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_state_947_ = lean_ctor_get(v_reader_946_, 0);
v_input_948_ = lean_ctor_get(v_reader_946_, 1);
v_messageCount_949_ = lean_ctor_get(v_reader_946_, 3);
v_bodyBytesRead_950_ = lean_ctor_get(v_reader_946_, 4);
v_headerBytesRead_951_ = lean_ctor_get(v_reader_946_, 5);
v_noMoreInput_952_ = lean_ctor_get_uint8(v_reader_946_, sizeof(void*)*6);
v_isSharedCheck_959_ = !lean_is_exclusive(v_reader_946_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_reader_946_, 2);
lean_dec(v_unused_960_);
v___x_954_ = v_reader_946_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_headerBytesRead_951_);
lean_inc(v_bodyBytesRead_950_);
lean_inc(v_messageCount_949_);
lean_inc(v_input_948_);
lean_inc(v_state_947_);
lean_dec(v_reader_946_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 2, v_messageHead_945_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_state_947_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_input_948_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_messageHead_945_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_messageCount_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v_bodyBytesRead_950_);
lean_ctor_set(v_reuseFailAlloc_958_, 5, v_headerBytesRead_951_);
lean_ctor_set_uint8(v_reuseFailAlloc_958_, sizeof(void*)*6, v_noMoreInput_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_961_, lean_object* v_messageHead_962_, lean_object* v_reader_963_){
_start:
{
lean_object* v_state_964_; lean_object* v_input_965_; lean_object* v_messageCount_966_; lean_object* v_bodyBytesRead_967_; lean_object* v_headerBytesRead_968_; uint8_t v_noMoreInput_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_state_964_ = lean_ctor_get(v_reader_963_, 0);
v_input_965_ = lean_ctor_get(v_reader_963_, 1);
v_messageCount_966_ = lean_ctor_get(v_reader_963_, 3);
v_bodyBytesRead_967_ = lean_ctor_get(v_reader_963_, 4);
v_headerBytesRead_968_ = lean_ctor_get(v_reader_963_, 5);
v_noMoreInput_969_ = lean_ctor_get_uint8(v_reader_963_, sizeof(void*)*6);
v_isSharedCheck_976_ = !lean_is_exclusive(v_reader_963_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_reader_963_, 2);
lean_dec(v_unused_977_);
v___x_971_ = v_reader_963_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_headerBytesRead_968_);
lean_inc(v_bodyBytesRead_967_);
lean_inc(v_messageCount_966_);
lean_inc(v_input_965_);
lean_inc(v_state_964_);
lean_dec(v_reader_963_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 2, v_messageHead_962_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_state_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_input_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_messageHead_962_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_messageCount_966_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_bodyBytesRead_967_);
lean_ctor_set(v_reuseFailAlloc_975_, 5, v_headerBytesRead_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*6, v_noMoreInput_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_978_, lean_object* v_messageHead_979_, lean_object* v_reader_980_){
_start:
{
uint8_t v_dir_boxed_981_; lean_object* v_res_982_; 
v_dir_boxed_981_ = lean_unbox(v_dir_978_);
v_res_982_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_981_, v_messageHead_979_, v_reader_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(lean_object* v_i_983_, lean_object* v_x_984_){
_start:
{
if (lean_obj_tag(v_x_984_) == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_mk_empty_array_with_capacity(v___x_985_);
v___x_987_ = lean_array_push(v___x_986_, v_i_983_);
v___x_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_val_989_ = lean_ctor_get(v_x_984_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_x_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_991_ = v_x_984_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_val_989_);
lean_dec(v_x_984_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = lean_array_push(v_val_989_, v_i_983_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_1000_, lean_object* v_name_1001_, lean_object* v_value_1002_, lean_object* v_reader_1003_){
_start:
{
if (v_dir_1000_ == 0)
{
lean_object* v_messageHead_1004_; lean_object* v_state_1005_; lean_object* v_input_1006_; lean_object* v_messageCount_1007_; lean_object* v_bodyBytesRead_1008_; lean_object* v_headerBytesRead_1009_; uint8_t v_noMoreInput_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1046_; 
v_messageHead_1004_ = lean_ctor_get(v_reader_1003_, 2);
v_state_1005_ = lean_ctor_get(v_reader_1003_, 0);
v_input_1006_ = lean_ctor_get(v_reader_1003_, 1);
v_messageCount_1007_ = lean_ctor_get(v_reader_1003_, 3);
v_bodyBytesRead_1008_ = lean_ctor_get(v_reader_1003_, 4);
v_headerBytesRead_1009_ = lean_ctor_get(v_reader_1003_, 5);
v_noMoreInput_1010_ = lean_ctor_get_uint8(v_reader_1003_, sizeof(void*)*6);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_reader_1003_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1012_ = v_reader_1003_;
v_isShared_1013_ = v_isSharedCheck_1046_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_headerBytesRead_1009_);
lean_inc(v_bodyBytesRead_1008_);
lean_inc(v_messageCount_1007_);
lean_inc(v_messageHead_1004_);
lean_inc(v_input_1006_);
lean_inc(v_state_1005_);
lean_dec(v_reader_1003_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1046_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v_method_1014_; uint8_t v_version_1015_; lean_object* v_uri_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1043_; 
v_method_1014_ = lean_ctor_get_uint8(v_messageHead_1004_, sizeof(void*)*2);
v_version_1015_ = lean_ctor_get_uint8(v_messageHead_1004_, sizeof(void*)*2 + 1);
v_uri_1016_ = lean_ctor_get(v_messageHead_1004_, 0);
lean_inc(v_uri_1016_);
v___x_1017_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1000_, v_messageHead_1004_);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_messageHead_1004_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1044_ = lean_ctor_get(v_messageHead_1004_, 1);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_messageHead_1004_, 0);
lean_dec(v_unused_1045_);
v___x_1019_ = v_messageHead_1004_;
v_isShared_1020_ = v_isSharedCheck_1043_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v_messageHead_1004_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1043_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_entries_1021_; lean_object* v_indexes_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1042_; 
v_entries_1021_ = lean_ctor_get(v___x_1017_, 0);
v_indexes_1022_ = lean_ctor_get(v___x_1017_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1024_ = v___x_1017_;
v_isShared_1025_ = v_isSharedCheck_1042_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_indexes_1022_);
lean_inc(v_entries_1021_);
lean_dec(v___x_1017_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1042_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v_i_1028_; lean_object* v_f_1029_; lean_object* v___x_1030_; lean_object* v_entries_1031_; lean_object* v_indexes_1032_; lean_object* v___x_1034_; 
v___f_1026_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1027_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1028_ = lean_array_get_size(v_entries_1021_);
v_f_1029_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1029_, 0, v_i_1028_);
lean_inc_ref(v_name_1001_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_name_1001_);
lean_ctor_set(v___x_1030_, 1, v_value_1002_);
v_entries_1031_ = lean_array_push(v_entries_1021_, v___x_1030_);
v_indexes_1032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1026_, v___f_1027_, v_indexes_1022_, v_name_1001_, v_f_1029_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_indexes_1032_);
lean_ctor_set(v___x_1024_, 0, v_entries_1031_);
v___x_1034_ = v___x_1024_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_entries_1031_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_indexes_1032_);
v___x_1034_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1034_);
v___x_1036_ = v___x_1019_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_uri_1016_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, sizeof(void*)*2, v_method_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, sizeof(void*)*2 + 1, v_version_1015_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v___x_1036_);
v___x_1038_ = v___x_1012_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_state_1005_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_input_1006_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_messageCount_1007_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_bodyBytesRead_1008_);
lean_ctor_set(v_reuseFailAlloc_1039_, 5, v_headerBytesRead_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1039_, sizeof(void*)*6, v_noMoreInput_1010_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
}
else
{
lean_object* v_messageHead_1047_; lean_object* v_state_1048_; lean_object* v_input_1049_; lean_object* v_messageCount_1050_; lean_object* v_bodyBytesRead_1051_; lean_object* v_headerBytesRead_1052_; uint8_t v_noMoreInput_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1088_; 
v_messageHead_1047_ = lean_ctor_get(v_reader_1003_, 2);
v_state_1048_ = lean_ctor_get(v_reader_1003_, 0);
v_input_1049_ = lean_ctor_get(v_reader_1003_, 1);
v_messageCount_1050_ = lean_ctor_get(v_reader_1003_, 3);
v_bodyBytesRead_1051_ = lean_ctor_get(v_reader_1003_, 4);
v_headerBytesRead_1052_ = lean_ctor_get(v_reader_1003_, 5);
v_noMoreInput_1053_ = lean_ctor_get_uint8(v_reader_1003_, sizeof(void*)*6);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_reader_1003_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1055_ = v_reader_1003_;
v_isShared_1056_ = v_isSharedCheck_1088_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_headerBytesRead_1052_);
lean_inc(v_bodyBytesRead_1051_);
lean_inc(v_messageCount_1050_);
lean_inc(v_messageHead_1047_);
lean_inc(v_input_1049_);
lean_inc(v_state_1048_);
lean_dec(v_reader_1003_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1088_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_status_1057_; uint8_t v_version_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1085_; 
v_status_1057_ = lean_ctor_get(v_messageHead_1047_, 0);
lean_inc(v_status_1057_);
v_version_1058_ = lean_ctor_get_uint8(v_messageHead_1047_, sizeof(void*)*2);
v___x_1059_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1000_, v_messageHead_1047_);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_messageHead_1047_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; lean_object* v_unused_1087_; 
v_unused_1086_ = lean_ctor_get(v_messageHead_1047_, 1);
lean_dec(v_unused_1086_);
v_unused_1087_ = lean_ctor_get(v_messageHead_1047_, 0);
lean_dec(v_unused_1087_);
v___x_1061_ = v_messageHead_1047_;
v_isShared_1062_ = v_isSharedCheck_1085_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v_messageHead_1047_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1085_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_entries_1063_; lean_object* v_indexes_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1084_; 
v_entries_1063_ = lean_ctor_get(v___x_1059_, 0);
v_indexes_1064_ = lean_ctor_get(v___x_1059_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1066_ = v___x_1059_;
v_isShared_1067_ = v_isSharedCheck_1084_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_indexes_1064_);
lean_inc(v_entries_1063_);
lean_dec(v___x_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1084_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v_i_1070_; lean_object* v_f_1071_; lean_object* v___x_1072_; lean_object* v_entries_1073_; lean_object* v_indexes_1074_; lean_object* v___x_1076_; 
v___f_1068_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1069_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1070_ = lean_array_get_size(v_entries_1063_);
v_f_1071_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1071_, 0, v_i_1070_);
lean_inc_ref(v_name_1001_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_name_1001_);
lean_ctor_set(v___x_1072_, 1, v_value_1002_);
v_entries_1073_ = lean_array_push(v_entries_1063_, v___x_1072_);
v_indexes_1074_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1068_, v___f_1069_, v_indexes_1064_, v_name_1001_, v_f_1071_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_indexes_1074_);
lean_ctor_set(v___x_1066_, 0, v_entries_1073_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_entries_1073_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_indexes_1074_);
v___x_1076_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1076_);
v___x_1078_ = v___x_1061_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_status_1057_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1076_);
lean_ctor_set_uint8(v_reuseFailAlloc_1082_, sizeof(void*)*2, v_version_1058_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 2, v___x_1078_);
v___x_1080_ = v___x_1055_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_state_1048_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_input_1049_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_messageCount_1050_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v_bodyBytesRead_1051_);
lean_ctor_set(v_reuseFailAlloc_1081_, 5, v_headerBytesRead_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*6, v_noMoreInput_1053_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1089_, lean_object* v_name_1090_, lean_object* v_value_1091_, lean_object* v_reader_1092_){
_start:
{
uint8_t v_dir_boxed_1093_; lean_object* v_res_1094_; 
v_dir_boxed_1093_ = lean_unbox(v_dir_1089_);
v_res_1094_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1093_, v_name_1090_, v_value_1091_, v_reader_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object* v_reader_1095_){
_start:
{
lean_object* v_input_1096_; lean_object* v_messageHead_1097_; lean_object* v_messageCount_1098_; lean_object* v_bodyBytesRead_1099_; lean_object* v_headerBytesRead_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v_input_1096_ = lean_ctor_get(v_reader_1095_, 1);
v_messageHead_1097_ = lean_ctor_get(v_reader_1095_, 2);
v_messageCount_1098_ = lean_ctor_get(v_reader_1095_, 3);
v_bodyBytesRead_1099_ = lean_ctor_get(v_reader_1095_, 4);
v_headerBytesRead_1100_ = lean_ctor_get(v_reader_1095_, 5);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_reader_1095_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_reader_1095_, 0);
lean_dec(v_unused_1110_);
v___x_1102_ = v_reader_1095_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_headerBytesRead_1100_);
lean_inc(v_bodyBytesRead_1099_);
lean_inc(v_messageCount_1098_);
lean_inc(v_messageHead_1097_);
lean_inc(v_input_1096_);
lean_dec(v_reader_1095_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = lean_box(6);
v___x_1105_ = 1;
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_input_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_messageHead_1097_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_messageCount_1098_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_bodyBytesRead_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_headerBytesRead_1100_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_ctor_set_uint8(v___x_1107_, sizeof(void*)*6, v___x_1105_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t v_dir_1111_, lean_object* v_reader_1112_){
_start:
{
lean_object* v_input_1113_; lean_object* v_messageHead_1114_; lean_object* v_messageCount_1115_; lean_object* v_bodyBytesRead_1116_; lean_object* v_headerBytesRead_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1126_; 
v_input_1113_ = lean_ctor_get(v_reader_1112_, 1);
v_messageHead_1114_ = lean_ctor_get(v_reader_1112_, 2);
v_messageCount_1115_ = lean_ctor_get(v_reader_1112_, 3);
v_bodyBytesRead_1116_ = lean_ctor_get(v_reader_1112_, 4);
v_headerBytesRead_1117_ = lean_ctor_get(v_reader_1112_, 5);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_reader_1112_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v_reader_1112_, 0);
lean_dec(v_unused_1127_);
v___x_1119_ = v_reader_1112_;
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_headerBytesRead_1117_);
lean_inc(v_bodyBytesRead_1116_);
lean_inc(v_messageCount_1115_);
lean_inc(v_messageHead_1114_);
lean_inc(v_input_1113_);
lean_dec(v_reader_1112_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1126_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1124_; 
v___x_1121_ = lean_box(6);
v___x_1122_ = 1;
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1121_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_input_1113_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_messageHead_1114_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_messageCount_1115_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v_bodyBytesRead_1116_);
lean_ctor_set(v_reuseFailAlloc_1125_, 5, v_headerBytesRead_1117_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_ctor_set_uint8(v___x_1124_, sizeof(void*)*6, v___x_1122_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object* v_dir_1128_, lean_object* v_reader_1129_){
_start:
{
uint8_t v_dir_boxed_1130_; lean_object* v_res_1131_; 
v_dir_boxed_1130_ = lean_unbox(v_dir_1128_);
v_res_1131_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_1130_, v_reader_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1132_){
_start:
{
lean_object* v_input_1133_; lean_object* v_messageHead_1134_; lean_object* v_messageCount_1135_; lean_object* v_bodyBytesRead_1136_; lean_object* v_headerBytesRead_1137_; uint8_t v_noMoreInput_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1148_; 
v_input_1133_ = lean_ctor_get(v_reader_1132_, 1);
v_messageHead_1134_ = lean_ctor_get(v_reader_1132_, 2);
v_messageCount_1135_ = lean_ctor_get(v_reader_1132_, 3);
v_bodyBytesRead_1136_ = lean_ctor_get(v_reader_1132_, 4);
v_headerBytesRead_1137_ = lean_ctor_get(v_reader_1132_, 5);
v_noMoreInput_1138_ = lean_ctor_get_uint8(v_reader_1132_, sizeof(void*)*6);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_reader_1132_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; 
v_unused_1149_ = lean_ctor_get(v_reader_1132_, 0);
lean_dec(v_unused_1149_);
v___x_1140_ = v_reader_1132_;
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_headerBytesRead_1137_);
lean_inc(v_bodyBytesRead_1136_);
lean_inc(v_messageCount_1135_);
lean_inc(v_messageHead_1134_);
lean_inc(v_input_1133_);
lean_dec(v_reader_1132_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1142_ = lean_box(5);
v___x_1143_ = lean_unsigned_to_nat(1u);
v___x_1144_ = lean_nat_add(v_messageCount_1135_, v___x_1143_);
lean_dec(v_messageCount_1135_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 3, v___x_1144_);
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1146_ = v___x_1140_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_input_1133_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_messageHead_1134_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_bodyBytesRead_1136_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_headerBytesRead_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*6, v_noMoreInput_1138_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1150_, lean_object* v_reader_1151_){
_start:
{
lean_object* v_input_1152_; lean_object* v_messageHead_1153_; lean_object* v_messageCount_1154_; lean_object* v_bodyBytesRead_1155_; lean_object* v_headerBytesRead_1156_; uint8_t v_noMoreInput_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1167_; 
v_input_1152_ = lean_ctor_get(v_reader_1151_, 1);
v_messageHead_1153_ = lean_ctor_get(v_reader_1151_, 2);
v_messageCount_1154_ = lean_ctor_get(v_reader_1151_, 3);
v_bodyBytesRead_1155_ = lean_ctor_get(v_reader_1151_, 4);
v_headerBytesRead_1156_ = lean_ctor_get(v_reader_1151_, 5);
v_noMoreInput_1157_ = lean_ctor_get_uint8(v_reader_1151_, sizeof(void*)*6);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_reader_1151_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v_reader_1151_, 0);
lean_dec(v_unused_1168_);
v___x_1159_ = v_reader_1151_;
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_headerBytesRead_1156_);
lean_inc(v_bodyBytesRead_1155_);
lean_inc(v_messageCount_1154_);
lean_inc(v_messageHead_1153_);
lean_inc(v_input_1152_);
lean_dec(v_reader_1151_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1161_ = lean_box(5);
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_messageCount_1154_, v___x_1162_);
lean_dec(v_messageCount_1154_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 3, v___x_1163_);
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1165_ = v___x_1159_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_input_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_messageHead_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_bodyBytesRead_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v_headerBytesRead_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*6, v_noMoreInput_1157_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object* v_dir_1169_, lean_object* v_reader_1170_){
_start:
{
uint8_t v_dir_boxed_1171_; lean_object* v_res_1172_; 
v_dir_boxed_1171_ = lean_unbox(v_dir_1169_);
v_res_1172_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_1171_, v_reader_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object* v_error_1173_, lean_object* v_reader_1174_){
_start:
{
lean_object* v_input_1175_; lean_object* v_messageHead_1176_; lean_object* v_messageCount_1177_; lean_object* v_bodyBytesRead_1178_; lean_object* v_headerBytesRead_1179_; uint8_t v_noMoreInput_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
v_input_1175_ = lean_ctor_get(v_reader_1174_, 1);
v_messageHead_1176_ = lean_ctor_get(v_reader_1174_, 2);
v_messageCount_1177_ = lean_ctor_get(v_reader_1174_, 3);
v_bodyBytesRead_1178_ = lean_ctor_get(v_reader_1174_, 4);
v_headerBytesRead_1179_ = lean_ctor_get(v_reader_1174_, 5);
v_noMoreInput_1180_ = lean_ctor_get_uint8(v_reader_1174_, sizeof(void*)*6);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_reader_1174_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_reader_1174_, 0);
lean_dec(v_unused_1189_);
v___x_1182_ = v_reader_1174_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_headerBytesRead_1179_);
lean_inc(v_bodyBytesRead_1178_);
lean_inc(v_messageCount_1177_);
lean_inc(v_messageHead_1176_);
lean_inc(v_input_1175_);
lean_dec(v_reader_1174_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_error_1173_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_input_1175_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_messageHead_1176_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_messageCount_1177_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_bodyBytesRead_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v_headerBytesRead_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1187_, sizeof(void*)*6, v_noMoreInput_1180_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t v_dir_1190_, lean_object* v_error_1191_, lean_object* v_reader_1192_){
_start:
{
lean_object* v_input_1193_; lean_object* v_messageHead_1194_; lean_object* v_messageCount_1195_; lean_object* v_bodyBytesRead_1196_; lean_object* v_headerBytesRead_1197_; uint8_t v_noMoreInput_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1206_; 
v_input_1193_ = lean_ctor_get(v_reader_1192_, 1);
v_messageHead_1194_ = lean_ctor_get(v_reader_1192_, 2);
v_messageCount_1195_ = lean_ctor_get(v_reader_1192_, 3);
v_bodyBytesRead_1196_ = lean_ctor_get(v_reader_1192_, 4);
v_headerBytesRead_1197_ = lean_ctor_get(v_reader_1192_, 5);
v_noMoreInput_1198_ = lean_ctor_get_uint8(v_reader_1192_, sizeof(void*)*6);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_reader_1192_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; 
v_unused_1207_ = lean_ctor_get(v_reader_1192_, 0);
lean_dec(v_unused_1207_);
v___x_1200_ = v_reader_1192_;
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_headerBytesRead_1197_);
lean_inc(v_bodyBytesRead_1196_);
lean_inc(v_messageCount_1195_);
lean_inc(v_messageHead_1194_);
lean_inc(v_input_1193_);
lean_dec(v_reader_1192_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_error_1191_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_input_1193_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_messageHead_1194_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_messageCount_1195_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_bodyBytesRead_1196_);
lean_ctor_set(v_reuseFailAlloc_1205_, 5, v_headerBytesRead_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1205_, sizeof(void*)*6, v_noMoreInput_1198_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object* v_dir_1208_, lean_object* v_error_1209_, lean_object* v_reader_1210_){
_start:
{
uint8_t v_dir_boxed_1211_; lean_object* v_res_1212_; 
v_dir_boxed_1211_ = lean_unbox(v_dir_1208_);
v_res_1212_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_1211_, v_error_1209_, v_reader_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1213_, lean_object* v_reader_1214_){
_start:
{
lean_object* v_input_1215_; lean_object* v_messageCount_1216_; uint8_t v_noMoreInput_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1227_; 
v_input_1215_ = lean_ctor_get(v_reader_1214_, 1);
v_messageCount_1216_ = lean_ctor_get(v_reader_1214_, 3);
v_noMoreInput_1217_ = lean_ctor_get_uint8(v_reader_1214_, sizeof(void*)*6);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_reader_1214_);
if (v_isSharedCheck_1227_ == 0)
{
lean_object* v_unused_1228_; lean_object* v_unused_1229_; lean_object* v_unused_1230_; lean_object* v_unused_1231_; 
v_unused_1228_ = lean_ctor_get(v_reader_1214_, 5);
lean_dec(v_unused_1228_);
v_unused_1229_ = lean_ctor_get(v_reader_1214_, 4);
lean_dec(v_unused_1229_);
v_unused_1230_ = lean_ctor_get(v_reader_1214_, 2);
lean_dec(v_unused_1230_);
v_unused_1231_ = lean_ctor_get(v_reader_1214_, 0);
lean_dec(v_unused_1231_);
v___x_1219_ = v_reader_1214_;
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_messageCount_1216_);
lean_inc(v_input_1215_);
lean_dec(v_reader_1214_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1213_);
v___x_1223_ = lean_unsigned_to_nat(0u);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 5, v___x_1223_);
lean_ctor_set(v___x_1219_, 4, v___x_1223_);
lean_ctor_set(v___x_1219_, 2, v___x_1222_);
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1225_ = v___x_1219_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_input_1215_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v_messageCount_1216_);
lean_ctor_set(v_reuseFailAlloc_1226_, 4, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 5, v___x_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*6, v_noMoreInput_1217_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1232_, lean_object* v_reader_1233_){
_start:
{
uint8_t v_dir_boxed_1234_; lean_object* v_res_1235_; 
v_dir_boxed_1234_ = lean_unbox(v_dir_1232_);
v_res_1235_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1234_, v_reader_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1236_){
_start:
{
lean_object* v_input_1237_; lean_object* v_state_1238_; uint8_t v_noMoreInput_1239_; lean_object* v_array_1240_; lean_object* v_idx_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_input_1237_ = lean_ctor_get(v_reader_1236_, 1);
v_state_1238_ = lean_ctor_get(v_reader_1236_, 0);
v_noMoreInput_1239_ = lean_ctor_get_uint8(v_reader_1236_, sizeof(void*)*6);
v_array_1240_ = lean_ctor_get(v_input_1237_, 0);
v_idx_1241_ = lean_ctor_get(v_input_1237_, 1);
v___x_1242_ = lean_byte_array_size(v_array_1240_);
v___x_1243_ = lean_nat_dec_le(v___x_1242_, v_idx_1241_);
if (v___x_1243_ == 0)
{
return v___x_1243_;
}
else
{
if (v_noMoreInput_1239_ == 0)
{
switch(lean_obj_tag(v_state_1238_))
{
case 5:
{
return v_noMoreInput_1239_;
}
case 6:
{
return v_noMoreInput_1239_;
}
case 7:
{
return v_noMoreInput_1239_;
}
case 3:
{
return v_noMoreInput_1239_;
}
default: 
{
return v___x_1243_;
}
}
}
else
{
uint8_t v___x_1244_; 
v___x_1244_ = 0;
return v___x_1244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1245_){
_start:
{
uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_res_1246_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1245_);
lean_dec_ref(v_reader_1245_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1248_, lean_object* v_reader_1249_){
_start:
{
lean_object* v_input_1250_; lean_object* v_state_1251_; uint8_t v_noMoreInput_1252_; lean_object* v_array_1253_; lean_object* v_idx_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_input_1250_ = lean_ctor_get(v_reader_1249_, 1);
v_state_1251_ = lean_ctor_get(v_reader_1249_, 0);
v_noMoreInput_1252_ = lean_ctor_get_uint8(v_reader_1249_, sizeof(void*)*6);
v_array_1253_ = lean_ctor_get(v_input_1250_, 0);
v_idx_1254_ = lean_ctor_get(v_input_1250_, 1);
v___x_1255_ = lean_byte_array_size(v_array_1253_);
v___x_1256_ = lean_nat_dec_le(v___x_1255_, v_idx_1254_);
if (v___x_1256_ == 0)
{
return v___x_1256_;
}
else
{
if (v_noMoreInput_1252_ == 0)
{
switch(lean_obj_tag(v_state_1251_))
{
case 5:
{
return v_noMoreInput_1252_;
}
case 6:
{
return v_noMoreInput_1252_;
}
case 7:
{
return v_noMoreInput_1252_;
}
case 3:
{
return v_noMoreInput_1252_;
}
default: 
{
return v___x_1256_;
}
}
}
else
{
uint8_t v___x_1257_; 
v___x_1257_ = 0;
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1258_, lean_object* v_reader_1259_){
_start:
{
uint8_t v_dir_boxed_1260_; uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_dir_boxed_1260_ = lean_unbox(v_dir_1258_);
v_res_1261_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1260_, v_reader_1259_);
lean_dec_ref(v_reader_1259_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object* v_reader_1263_){
_start:
{
lean_object* v_state_1264_; 
v_state_1264_ = lean_ctor_get(v_reader_1263_, 0);
lean_inc(v_state_1264_);
lean_dec_ref(v_reader_1263_);
if (lean_obj_tag(v_state_1264_) == 7)
{
lean_object* v_error_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_error_1265_ = lean_ctor_get(v_state_1264_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_state_1264_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v_state_1264_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_error_1265_);
lean_dec(v_state_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 1);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_error_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
else
{
lean_object* v___x_1273_; 
lean_dec(v_state_1264_);
v___x_1273_ = lean_box(0);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t v_dir_1274_, lean_object* v_reader_1275_){
_start:
{
lean_object* v_state_1276_; 
v_state_1276_ = lean_ctor_get(v_reader_1275_, 0);
lean_inc(v_state_1276_);
lean_dec_ref(v_reader_1275_);
if (lean_obj_tag(v_state_1276_) == 7)
{
lean_object* v_error_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_error_1277_ = lean_ctor_get(v_state_1276_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_state_1276_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v_state_1276_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_error_1277_);
lean_dec(v_state_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 1);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_error_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_state_1276_);
v___x_1285_ = lean_box(0);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object* v_dir_1286_, lean_object* v_reader_1287_){
_start:
{
uint8_t v_dir_boxed_1288_; lean_object* v_res_1289_; 
v_dir_boxed_1288_ = lean_unbox(v_dir_1286_);
v_res_1289_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_1288_, v_reader_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1290_){
_start:
{
lean_object* v_input_1291_; lean_object* v_array_1292_; lean_object* v_idx_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_input_1291_ = lean_ctor_get(v_reader_1290_, 1);
v_array_1292_ = lean_ctor_get(v_input_1291_, 0);
v_idx_1293_ = lean_ctor_get(v_input_1291_, 1);
v___x_1294_ = lean_byte_array_size(v_array_1292_);
v___x_1295_ = lean_nat_sub(v___x_1294_, v_idx_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1296_);
lean_dec_ref(v_reader_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1298_, lean_object* v_reader_1299_){
_start:
{
lean_object* v_input_1300_; lean_object* v_array_1301_; lean_object* v_idx_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_input_1300_ = lean_ctor_get(v_reader_1299_, 1);
v_array_1301_ = lean_ctor_get(v_input_1300_, 0);
v_idx_1302_ = lean_ctor_get(v_input_1300_, 1);
v___x_1303_ = lean_byte_array_size(v_array_1301_);
v___x_1304_ = lean_nat_sub(v___x_1303_, v_idx_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1305_, lean_object* v_reader_1306_){
_start:
{
uint8_t v_dir_boxed_1307_; lean_object* v_res_1308_; 
v_dir_boxed_1307_ = lean_unbox(v_dir_1305_);
v_res_1308_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1307_, v_reader_1306_);
lean_dec_ref(v_reader_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1309_, lean_object* v_reader_1310_){
_start:
{
lean_object* v_input_1311_; lean_object* v_state_1312_; lean_object* v_messageHead_1313_; lean_object* v_messageCount_1314_; lean_object* v_bodyBytesRead_1315_; lean_object* v_headerBytesRead_1316_; uint8_t v_noMoreInput_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1334_; 
v_input_1311_ = lean_ctor_get(v_reader_1310_, 1);
v_state_1312_ = lean_ctor_get(v_reader_1310_, 0);
v_messageHead_1313_ = lean_ctor_get(v_reader_1310_, 2);
v_messageCount_1314_ = lean_ctor_get(v_reader_1310_, 3);
v_bodyBytesRead_1315_ = lean_ctor_get(v_reader_1310_, 4);
v_headerBytesRead_1316_ = lean_ctor_get(v_reader_1310_, 5);
v_noMoreInput_1317_ = lean_ctor_get_uint8(v_reader_1310_, sizeof(void*)*6);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_reader_1310_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1319_ = v_reader_1310_;
v_isShared_1320_ = v_isSharedCheck_1334_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_headerBytesRead_1316_);
lean_inc(v_bodyBytesRead_1315_);
lean_inc(v_messageCount_1314_);
lean_inc(v_messageHead_1313_);
lean_inc(v_input_1311_);
lean_inc(v_state_1312_);
lean_dec(v_reader_1310_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1334_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_array_1321_; lean_object* v_idx_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1333_; 
v_array_1321_ = lean_ctor_get(v_input_1311_, 0);
v_idx_1322_ = lean_ctor_get(v_input_1311_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_input_1311_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1324_ = v_input_1311_;
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_idx_1322_);
lean_inc(v_array_1321_);
lean_dec(v_input_1311_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_nat_add(v_idx_1322_, v_n_1309_);
lean_dec(v_idx_1322_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_array_1321_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 1, v___x_1328_);
v___x_1330_ = v___x_1319_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_state_1312_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_messageHead_1313_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_messageCount_1314_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_bodyBytesRead_1315_);
lean_ctor_set(v_reuseFailAlloc_1331_, 5, v_headerBytesRead_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*6, v_noMoreInput_1317_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1335_, lean_object* v_reader_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1335_, v_reader_1336_);
lean_dec(v_n_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1338_, lean_object* v_n_1339_, lean_object* v_reader_1340_){
_start:
{
lean_object* v_input_1341_; lean_object* v_state_1342_; lean_object* v_messageHead_1343_; lean_object* v_messageCount_1344_; lean_object* v_bodyBytesRead_1345_; lean_object* v_headerBytesRead_1346_; uint8_t v_noMoreInput_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1364_; 
v_input_1341_ = lean_ctor_get(v_reader_1340_, 1);
v_state_1342_ = lean_ctor_get(v_reader_1340_, 0);
v_messageHead_1343_ = lean_ctor_get(v_reader_1340_, 2);
v_messageCount_1344_ = lean_ctor_get(v_reader_1340_, 3);
v_bodyBytesRead_1345_ = lean_ctor_get(v_reader_1340_, 4);
v_headerBytesRead_1346_ = lean_ctor_get(v_reader_1340_, 5);
v_noMoreInput_1347_ = lean_ctor_get_uint8(v_reader_1340_, sizeof(void*)*6);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_reader_1340_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1349_ = v_reader_1340_;
v_isShared_1350_ = v_isSharedCheck_1364_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_headerBytesRead_1346_);
lean_inc(v_bodyBytesRead_1345_);
lean_inc(v_messageCount_1344_);
lean_inc(v_messageHead_1343_);
lean_inc(v_input_1341_);
lean_inc(v_state_1342_);
lean_dec(v_reader_1340_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1364_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_array_1351_; lean_object* v_idx_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1363_; 
v_array_1351_ = lean_ctor_get(v_input_1341_, 0);
v_idx_1352_ = lean_ctor_get(v_input_1341_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_input_1341_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1354_ = v_input_1341_;
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_idx_1352_);
lean_inc(v_array_1351_);
lean_dec(v_input_1341_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1363_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_nat_add(v_idx_1352_, v_n_1339_);
lean_dec(v_idx_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_array_1351_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1360_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1358_);
v___x_1360_ = v___x_1349_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_state_1342_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_messageHead_1343_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_messageCount_1344_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_bodyBytesRead_1345_);
lean_ctor_set(v_reuseFailAlloc_1361_, 5, v_headerBytesRead_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1361_, sizeof(void*)*6, v_noMoreInput_1347_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1365_, lean_object* v_n_1366_, lean_object* v_reader_1367_){
_start:
{
uint8_t v_dir_boxed_1368_; lean_object* v_res_1369_; 
v_dir_boxed_1368_ = lean_unbox(v_dir_1365_);
v_res_1369_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1368_, v_n_1366_, v_reader_1367_);
lean_dec(v_n_1366_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1372_){
_start:
{
lean_object* v_input_1373_; lean_object* v_messageHead_1374_; lean_object* v_messageCount_1375_; uint8_t v_noMoreInput_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1385_; 
v_input_1373_ = lean_ctor_get(v_reader_1372_, 1);
v_messageHead_1374_ = lean_ctor_get(v_reader_1372_, 2);
v_messageCount_1375_ = lean_ctor_get(v_reader_1372_, 3);
v_noMoreInput_1376_ = lean_ctor_get_uint8(v_reader_1372_, sizeof(void*)*6);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_reader_1372_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; lean_object* v_unused_1387_; lean_object* v_unused_1388_; 
v_unused_1386_ = lean_ctor_get(v_reader_1372_, 5);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_reader_1372_, 4);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_reader_1372_, 0);
lean_dec(v_unused_1388_);
v___x_1378_ = v_reader_1372_;
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_messageCount_1375_);
lean_inc(v_messageHead_1374_);
lean_inc(v_input_1373_);
lean_dec(v_reader_1372_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1385_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 5, v___x_1380_);
lean_ctor_set(v___x_1378_, 4, v___x_1380_);
lean_ctor_set(v___x_1378_, 0, v___x_1381_);
v___x_1383_ = v___x_1378_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_input_1373_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_messageHead_1374_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_messageCount_1375_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1384_, 5, v___x_1380_);
lean_ctor_set_uint8(v_reuseFailAlloc_1384_, sizeof(void*)*6, v_noMoreInput_1376_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1389_, lean_object* v_reader_1390_){
_start:
{
lean_object* v_input_1391_; lean_object* v_messageHead_1392_; lean_object* v_messageCount_1393_; uint8_t v_noMoreInput_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1403_; 
v_input_1391_ = lean_ctor_get(v_reader_1390_, 1);
v_messageHead_1392_ = lean_ctor_get(v_reader_1390_, 2);
v_messageCount_1393_ = lean_ctor_get(v_reader_1390_, 3);
v_noMoreInput_1394_ = lean_ctor_get_uint8(v_reader_1390_, sizeof(void*)*6);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_reader_1390_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; 
v_unused_1404_ = lean_ctor_get(v_reader_1390_, 5);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_reader_1390_, 4);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_reader_1390_, 0);
lean_dec(v_unused_1406_);
v___x_1396_ = v_reader_1390_;
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_messageCount_1393_);
lean_inc(v_messageHead_1392_);
lean_inc(v_input_1391_);
lean_dec(v_reader_1390_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1398_ = lean_unsigned_to_nat(0u);
v___x_1399_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 5, v___x_1398_);
lean_ctor_set(v___x_1396_, 4, v___x_1398_);
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_input_1391_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_messageHead_1392_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_messageCount_1393_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1402_, 5, v___x_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*6, v_noMoreInput_1394_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1407_, lean_object* v_reader_1408_){
_start:
{
uint8_t v_dir_boxed_1409_; lean_object* v_res_1410_; 
v_dir_boxed_1409_ = lean_unbox(v_dir_1407_);
v_res_1410_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1409_, v_reader_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1411_, lean_object* v_reader_1412_){
_start:
{
lean_object* v_state_1413_; lean_object* v_input_1414_; lean_object* v_messageHead_1415_; lean_object* v_messageCount_1416_; lean_object* v_bodyBytesRead_1417_; lean_object* v_headerBytesRead_1418_; uint8_t v_noMoreInput_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
v_state_1413_ = lean_ctor_get(v_reader_1412_, 0);
v_input_1414_ = lean_ctor_get(v_reader_1412_, 1);
v_messageHead_1415_ = lean_ctor_get(v_reader_1412_, 2);
v_messageCount_1416_ = lean_ctor_get(v_reader_1412_, 3);
v_bodyBytesRead_1417_ = lean_ctor_get(v_reader_1412_, 4);
v_headerBytesRead_1418_ = lean_ctor_get(v_reader_1412_, 5);
v_noMoreInput_1419_ = lean_ctor_get_uint8(v_reader_1412_, sizeof(void*)*6);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_reader_1412_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1421_ = v_reader_1412_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_headerBytesRead_1418_);
lean_inc(v_bodyBytesRead_1417_);
lean_inc(v_messageCount_1416_);
lean_inc(v_messageHead_1415_);
lean_inc(v_input_1414_);
lean_inc(v_state_1413_);
lean_dec(v_reader_1412_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_nat_add(v_bodyBytesRead_1417_, v_n_1411_);
lean_dec(v_bodyBytesRead_1417_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 4, v___x_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_state_1413_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_input_1414_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_messageHead_1415_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_messageCount_1416_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1426_, 5, v_headerBytesRead_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1426_, sizeof(void*)*6, v_noMoreInput_1419_);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1428_, lean_object* v_reader_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1428_, v_reader_1429_);
lean_dec(v_n_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1431_, lean_object* v_n_1432_, lean_object* v_reader_1433_){
_start:
{
lean_object* v_state_1434_; lean_object* v_input_1435_; lean_object* v_messageHead_1436_; lean_object* v_messageCount_1437_; lean_object* v_bodyBytesRead_1438_; lean_object* v_headerBytesRead_1439_; uint8_t v_noMoreInput_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_state_1434_ = lean_ctor_get(v_reader_1433_, 0);
v_input_1435_ = lean_ctor_get(v_reader_1433_, 1);
v_messageHead_1436_ = lean_ctor_get(v_reader_1433_, 2);
v_messageCount_1437_ = lean_ctor_get(v_reader_1433_, 3);
v_bodyBytesRead_1438_ = lean_ctor_get(v_reader_1433_, 4);
v_headerBytesRead_1439_ = lean_ctor_get(v_reader_1433_, 5);
v_noMoreInput_1440_ = lean_ctor_get_uint8(v_reader_1433_, sizeof(void*)*6);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_reader_1433_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v_reader_1433_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_headerBytesRead_1439_);
lean_inc(v_bodyBytesRead_1438_);
lean_inc(v_messageCount_1437_);
lean_inc(v_messageHead_1436_);
lean_inc(v_input_1435_);
lean_inc(v_state_1434_);
lean_dec(v_reader_1433_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_nat_add(v_bodyBytesRead_1438_, v_n_1432_);
lean_dec(v_bodyBytesRead_1438_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 4, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_state_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_input_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_messageHead_1436_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_messageCount_1437_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v_headerBytesRead_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*6, v_noMoreInput_1440_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1449_, lean_object* v_n_1450_, lean_object* v_reader_1451_){
_start:
{
uint8_t v_dir_boxed_1452_; lean_object* v_res_1453_; 
v_dir_boxed_1452_ = lean_unbox(v_dir_1449_);
v_res_1453_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1452_, v_n_1450_, v_reader_1451_);
lean_dec(v_n_1450_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1454_, lean_object* v_reader_1455_){
_start:
{
lean_object* v_state_1456_; lean_object* v_input_1457_; lean_object* v_messageHead_1458_; lean_object* v_messageCount_1459_; lean_object* v_bodyBytesRead_1460_; lean_object* v_headerBytesRead_1461_; uint8_t v_noMoreInput_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_state_1456_ = lean_ctor_get(v_reader_1455_, 0);
v_input_1457_ = lean_ctor_get(v_reader_1455_, 1);
v_messageHead_1458_ = lean_ctor_get(v_reader_1455_, 2);
v_messageCount_1459_ = lean_ctor_get(v_reader_1455_, 3);
v_bodyBytesRead_1460_ = lean_ctor_get(v_reader_1455_, 4);
v_headerBytesRead_1461_ = lean_ctor_get(v_reader_1455_, 5);
v_noMoreInput_1462_ = lean_ctor_get_uint8(v_reader_1455_, sizeof(void*)*6);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_reader_1455_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_reader_1455_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_headerBytesRead_1461_);
lean_inc(v_bodyBytesRead_1460_);
lean_inc(v_messageCount_1459_);
lean_inc(v_messageHead_1458_);
lean_inc(v_input_1457_);
lean_inc(v_state_1456_);
lean_dec(v_reader_1455_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_nat_add(v_headerBytesRead_1461_, v_n_1454_);
lean_dec(v_headerBytesRead_1461_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 5, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_state_1456_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_input_1457_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_messageHead_1458_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_messageCount_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_bodyBytesRead_1460_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v___x_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*6, v_noMoreInput_1462_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1471_, lean_object* v_reader_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1471_, v_reader_1472_);
lean_dec(v_n_1471_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1474_, lean_object* v_n_1475_, lean_object* v_reader_1476_){
_start:
{
lean_object* v_state_1477_; lean_object* v_input_1478_; lean_object* v_messageHead_1479_; lean_object* v_messageCount_1480_; lean_object* v_bodyBytesRead_1481_; lean_object* v_headerBytesRead_1482_; uint8_t v_noMoreInput_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1491_; 
v_state_1477_ = lean_ctor_get(v_reader_1476_, 0);
v_input_1478_ = lean_ctor_get(v_reader_1476_, 1);
v_messageHead_1479_ = lean_ctor_get(v_reader_1476_, 2);
v_messageCount_1480_ = lean_ctor_get(v_reader_1476_, 3);
v_bodyBytesRead_1481_ = lean_ctor_get(v_reader_1476_, 4);
v_headerBytesRead_1482_ = lean_ctor_get(v_reader_1476_, 5);
v_noMoreInput_1483_ = lean_ctor_get_uint8(v_reader_1476_, sizeof(void*)*6);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_reader_1476_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1485_ = v_reader_1476_;
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_headerBytesRead_1482_);
lean_inc(v_bodyBytesRead_1481_);
lean_inc(v_messageCount_1480_);
lean_inc(v_messageHead_1479_);
lean_inc(v_input_1478_);
lean_inc(v_state_1477_);
lean_dec(v_reader_1476_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_nat_add(v_headerBytesRead_1482_, v_n_1475_);
lean_dec(v_headerBytesRead_1482_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 5, v___x_1487_);
v___x_1489_ = v___x_1485_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_state_1477_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_input_1478_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_messageHead_1479_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_messageCount_1480_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_bodyBytesRead_1481_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v___x_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1490_, sizeof(void*)*6, v_noMoreInput_1483_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1492_, lean_object* v_n_1493_, lean_object* v_reader_1494_){
_start:
{
uint8_t v_dir_boxed_1495_; lean_object* v_res_1496_; 
v_dir_boxed_1495_ = lean_unbox(v_dir_1492_);
v_res_1496_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1495_, v_n_1493_, v_reader_1494_);
lean_dec(v_n_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1497_, lean_object* v_reader_1498_){
_start:
{
lean_object* v_input_1499_; lean_object* v_messageHead_1500_; lean_object* v_messageCount_1501_; lean_object* v_bodyBytesRead_1502_; lean_object* v_headerBytesRead_1503_; uint8_t v_noMoreInput_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1513_; 
v_input_1499_ = lean_ctor_get(v_reader_1498_, 1);
v_messageHead_1500_ = lean_ctor_get(v_reader_1498_, 2);
v_messageCount_1501_ = lean_ctor_get(v_reader_1498_, 3);
v_bodyBytesRead_1502_ = lean_ctor_get(v_reader_1498_, 4);
v_headerBytesRead_1503_ = lean_ctor_get(v_reader_1498_, 5);
v_noMoreInput_1504_ = lean_ctor_get_uint8(v_reader_1498_, sizeof(void*)*6);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_reader_1498_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_reader_1498_, 0);
lean_dec(v_unused_1514_);
v___x_1506_ = v_reader_1498_;
v_isShared_1507_ = v_isSharedCheck_1513_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_headerBytesRead_1503_);
lean_inc(v_bodyBytesRead_1502_);
lean_inc(v_messageCount_1501_);
lean_inc(v_messageHead_1500_);
lean_inc(v_input_1499_);
lean_dec(v_reader_1498_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1513_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v_size_1497_);
v___x_1509_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_input_1499_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_messageHead_1500_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_messageCount_1501_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_bodyBytesRead_1502_);
lean_ctor_set(v_reuseFailAlloc_1512_, 5, v_headerBytesRead_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1512_, sizeof(void*)*6, v_noMoreInput_1504_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1515_, lean_object* v_size_1516_, lean_object* v_reader_1517_){
_start:
{
lean_object* v_input_1518_; lean_object* v_messageHead_1519_; lean_object* v_messageCount_1520_; lean_object* v_bodyBytesRead_1521_; lean_object* v_headerBytesRead_1522_; uint8_t v_noMoreInput_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1532_; 
v_input_1518_ = lean_ctor_get(v_reader_1517_, 1);
v_messageHead_1519_ = lean_ctor_get(v_reader_1517_, 2);
v_messageCount_1520_ = lean_ctor_get(v_reader_1517_, 3);
v_bodyBytesRead_1521_ = lean_ctor_get(v_reader_1517_, 4);
v_headerBytesRead_1522_ = lean_ctor_get(v_reader_1517_, 5);
v_noMoreInput_1523_ = lean_ctor_get_uint8(v_reader_1517_, sizeof(void*)*6);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_reader_1517_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v_reader_1517_, 0);
lean_dec(v_unused_1533_);
v___x_1525_ = v_reader_1517_;
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_headerBytesRead_1522_);
lean_inc(v_bodyBytesRead_1521_);
lean_inc(v_messageCount_1520_);
lean_inc(v_messageHead_1519_);
lean_inc(v_input_1518_);
lean_dec(v_reader_1517_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1532_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_size_1516_);
v___x_1528_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 0, v___x_1528_);
v___x_1530_ = v___x_1525_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_input_1518_);
lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_messageHead_1519_);
lean_ctor_set(v_reuseFailAlloc_1531_, 3, v_messageCount_1520_);
lean_ctor_set(v_reuseFailAlloc_1531_, 4, v_bodyBytesRead_1521_);
lean_ctor_set(v_reuseFailAlloc_1531_, 5, v_headerBytesRead_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1531_, sizeof(void*)*6, v_noMoreInput_1523_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1534_, lean_object* v_size_1535_, lean_object* v_reader_1536_){
_start:
{
uint8_t v_dir_boxed_1537_; lean_object* v_res_1538_; 
v_dir_boxed_1537_ = lean_unbox(v_dir_1534_);
v_res_1538_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1537_, v_size_1535_, v_reader_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1541_){
_start:
{
lean_object* v_input_1542_; lean_object* v_messageHead_1543_; lean_object* v_messageCount_1544_; lean_object* v_bodyBytesRead_1545_; lean_object* v_headerBytesRead_1546_; uint8_t v_noMoreInput_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_input_1542_ = lean_ctor_get(v_reader_1541_, 1);
v_messageHead_1543_ = lean_ctor_get(v_reader_1541_, 2);
v_messageCount_1544_ = lean_ctor_get(v_reader_1541_, 3);
v_bodyBytesRead_1545_ = lean_ctor_get(v_reader_1541_, 4);
v_headerBytesRead_1546_ = lean_ctor_get(v_reader_1541_, 5);
v_noMoreInput_1547_ = lean_ctor_get_uint8(v_reader_1541_, sizeof(void*)*6);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_reader_1541_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_reader_1541_, 0);
lean_dec(v_unused_1556_);
v___x_1549_ = v_reader_1541_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_headerBytesRead_1546_);
lean_inc(v_bodyBytesRead_1545_);
lean_inc(v_messageCount_1544_);
lean_inc(v_messageHead_1543_);
lean_inc(v_input_1542_);
lean_dec(v_reader_1541_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_input_1542_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_messageHead_1543_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_messageCount_1544_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_bodyBytesRead_1545_);
lean_ctor_set(v_reuseFailAlloc_1554_, 5, v_headerBytesRead_1546_);
lean_ctor_set_uint8(v_reuseFailAlloc_1554_, sizeof(void*)*6, v_noMoreInput_1547_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1557_, lean_object* v_reader_1558_){
_start:
{
lean_object* v_input_1559_; lean_object* v_messageHead_1560_; lean_object* v_messageCount_1561_; lean_object* v_bodyBytesRead_1562_; lean_object* v_headerBytesRead_1563_; uint8_t v_noMoreInput_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_input_1559_ = lean_ctor_get(v_reader_1558_, 1);
v_messageHead_1560_ = lean_ctor_get(v_reader_1558_, 2);
v_messageCount_1561_ = lean_ctor_get(v_reader_1558_, 3);
v_bodyBytesRead_1562_ = lean_ctor_get(v_reader_1558_, 4);
v_headerBytesRead_1563_ = lean_ctor_get(v_reader_1558_, 5);
v_noMoreInput_1564_ = lean_ctor_get_uint8(v_reader_1558_, sizeof(void*)*6);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_reader_1558_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_reader_1558_, 0);
lean_dec(v_unused_1573_);
v___x_1566_ = v_reader_1558_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_headerBytesRead_1563_);
lean_inc(v_bodyBytesRead_1562_);
lean_inc(v_messageCount_1561_);
lean_inc(v_messageHead_1560_);
lean_inc(v_input_1559_);
lean_dec(v_reader_1558_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_input_1559_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_messageHead_1560_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_messageCount_1561_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_bodyBytesRead_1562_);
lean_ctor_set(v_reuseFailAlloc_1571_, 5, v_headerBytesRead_1563_);
lean_ctor_set_uint8(v_reuseFailAlloc_1571_, sizeof(void*)*6, v_noMoreInput_1564_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1574_, lean_object* v_reader_1575_){
_start:
{
uint8_t v_dir_boxed_1576_; lean_object* v_res_1577_; 
v_dir_boxed_1576_ = lean_unbox(v_dir_1574_);
v_res_1577_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1576_, v_reader_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object* v_reader_1578_){
_start:
{
lean_object* v_state_1579_; lean_object* v_input_1580_; lean_object* v_messageHead_1581_; lean_object* v_messageCount_1582_; lean_object* v_bodyBytesRead_1583_; lean_object* v_headerBytesRead_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_state_1579_ = lean_ctor_get(v_reader_1578_, 0);
v_input_1580_ = lean_ctor_get(v_reader_1578_, 1);
v_messageHead_1581_ = lean_ctor_get(v_reader_1578_, 2);
v_messageCount_1582_ = lean_ctor_get(v_reader_1578_, 3);
v_bodyBytesRead_1583_ = lean_ctor_get(v_reader_1578_, 4);
v_headerBytesRead_1584_ = lean_ctor_get(v_reader_1578_, 5);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_reader_1578_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1586_ = v_reader_1578_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_headerBytesRead_1584_);
lean_inc(v_bodyBytesRead_1583_);
lean_inc(v_messageCount_1582_);
lean_inc(v_messageHead_1581_);
lean_inc(v_input_1580_);
lean_inc(v_state_1579_);
lean_dec(v_reader_1578_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
uint8_t v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = 1;
if (v_isShared_1587_ == 0)
{
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_state_1579_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_input_1580_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_messageHead_1581_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_messageCount_1582_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_bodyBytesRead_1583_);
lean_ctor_set(v_reuseFailAlloc_1591_, 5, v_headerBytesRead_1584_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*6, v___x_1588_);
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t v_dir_1593_, lean_object* v_reader_1594_){
_start:
{
lean_object* v_state_1595_; lean_object* v_input_1596_; lean_object* v_messageHead_1597_; lean_object* v_messageCount_1598_; lean_object* v_bodyBytesRead_1599_; lean_object* v_headerBytesRead_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
v_state_1595_ = lean_ctor_get(v_reader_1594_, 0);
v_input_1596_ = lean_ctor_get(v_reader_1594_, 1);
v_messageHead_1597_ = lean_ctor_get(v_reader_1594_, 2);
v_messageCount_1598_ = lean_ctor_get(v_reader_1594_, 3);
v_bodyBytesRead_1599_ = lean_ctor_get(v_reader_1594_, 4);
v_headerBytesRead_1600_ = lean_ctor_get(v_reader_1594_, 5);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_reader_1594_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1602_ = v_reader_1594_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_headerBytesRead_1600_);
lean_inc(v_bodyBytesRead_1599_);
lean_inc(v_messageCount_1598_);
lean_inc(v_messageHead_1597_);
lean_inc(v_input_1596_);
lean_inc(v_state_1595_);
lean_dec(v_reader_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
uint8_t v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = 1;
if (v_isShared_1603_ == 0)
{
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_state_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_input_1596_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_messageHead_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_messageCount_1598_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_bodyBytesRead_1599_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v_headerBytesRead_1600_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*6, v___x_1604_);
return v___x_1606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object* v_dir_1609_, lean_object* v_reader_1610_){
_start:
{
uint8_t v_dir_boxed_1611_; lean_object* v_res_1612_; 
v_dir_boxed_1611_ = lean_unbox(v_dir_1609_);
v_res_1612_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_1611_, v_reader_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1613_, lean_object* v_reader_1614_){
_start:
{
lean_object* v_messageHead_1615_; uint8_t v___x_1616_; 
v_messageHead_1615_ = lean_ctor_get(v_reader_1614_, 2);
v___x_1616_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1613_, v_messageHead_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1617_, lean_object* v_reader_1618_){
_start:
{
uint8_t v_dir_boxed_1619_; uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_dir_boxed_1619_ = lean_unbox(v_dir_1617_);
v_res_1620_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1619_, v_reader_1618_);
lean_dec_ref(v_reader_1618_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Internal(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Parser(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1_Error(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Protocol_H1_Reader(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
