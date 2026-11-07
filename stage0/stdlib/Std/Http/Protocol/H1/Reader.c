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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instReprError_repr(lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_trailers_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_trailers_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Std.Http.Protocol.H1.Reader.BodyState.trailers"};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__12 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__12_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__12_value)}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__13 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__13_value;
static const lean_ctor_object l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__14 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__14_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instReprBodyState___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0 = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState = (const lean_object*)&l_Std_Http_Protocol_H1_Reader_instBEqBodyState___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_remaining_7_; lean_object* v___x_8_; 
v_remaining_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_remaining_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_remaining_7_);
return v___x_8_;
}
case 2:
{
lean_object* v_ext_9_; lean_object* v_remaining_10_; lean_object* v___x_11_; 
v_ext_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_ext_9_);
v_remaining_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_remaining_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_ext_9_, v_remaining_10_);
return v___x_11_;
}
case 3:
{
lean_object* v_ext_12_; lean_object* v_count_13_; lean_object* v___x_14_; 
v_ext_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_ext_12_);
v_count_13_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_count_13_);
lean_dec_ref_known(v_t_5_, 2);
v___x_14_ = lean_apply_2(v_k_6_, v_ext_12_, v_count_13_);
return v___x_14_;
}
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_trailers_elim___redArg(lean_object* v_t_51_, lean_object* v_trailers_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_51_, v_trailers_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_trailers_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_trailers_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_55_, v_trailers_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim___redArg(lean_object* v_t_59_, lean_object* v_closeDelimited_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_59_, v_closeDelimited_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_closeDelimited_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_63_, v_closeDelimited_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
if (lean_obj_tag(v_x_77_) == 0)
{
lean_object* v___x_79_; 
v___x_79_ = ((lean_object*)(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_79_;
}
else
{
lean_object* v_val_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_val_80_ = lean_ctor_get(v_x_77_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v_x_77_, 1);
v___x_81_ = ((lean_object*)(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3));
v___x_82_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_val_80_);
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = l_Repr_addAppParen(v___x_83_, v_x_78_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_x_85_, v_x_86_);
lean_dec(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_dec(v_x_88_);
return v_x_89_;
}
else
{
lean_object* v_head_91_; lean_object* v_tail_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_101_; 
v_head_91_ = lean_ctor_get(v_x_90_, 0);
v_tail_92_ = lean_ctor_get(v_x_90_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_101_ == 0)
{
v___x_94_ = v_x_90_;
v_isShared_95_ = v_isSharedCheck_101_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_tail_92_);
lean_inc(v_head_91_);
lean_dec(v_x_90_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_101_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
lean_inc(v_x_88_);
if (v_isShared_95_ == 0)
{
lean_ctor_set_tag(v___x_94_, 5);
lean_ctor_set(v___x_94_, 1, v_x_88_);
lean_ctor_set(v___x_94_, 0, v_x_89_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_x_89_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_x_88_);
v___x_97_ = v_reuseFailAlloc_100_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_head_91_);
v_x_89_ = v___x_98_;
v_x_90_ = v_tail_92_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
if (lean_obj_tag(v_x_102_) == 0)
{
lean_object* v___x_104_; 
lean_dec(v_x_103_);
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v_tail_105_; 
v_tail_105_ = lean_ctor_get(v_x_102_, 1);
if (lean_obj_tag(v_tail_105_) == 0)
{
lean_object* v_head_106_; 
lean_dec(v_x_103_);
v_head_106_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_head_106_);
lean_dec_ref_known(v_x_102_, 2);
return v_head_106_;
}
else
{
lean_object* v_head_107_; lean_object* v___x_108_; 
lean_inc(v_tail_105_);
v_head_107_ = lean_ctor_get(v_x_102_, 0);
lean_inc(v_head_107_);
lean_dec_ref_known(v_x_102_, 2);
v___x_108_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(v_x_103_, v_head_107_, v_tail_105_);
return v___x_108_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0));
v___x_118_ = lean_string_length(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(lean_object* v_x_125_){
_start:
{
lean_object* v_fst_126_; lean_object* v_snd_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_150_; 
v_fst_126_ = lean_ctor_get(v_x_125_, 0);
v_snd_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_150_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snd_127_);
lean_inc(v_fst_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_150_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_fst_126_);
v___x_133_ = lean_box(0);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 1, v___x_133_);
lean_ctor_set(v___x_129_, 0, v___x_132_);
v___x_135_ = v___x_129_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_149_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; 
v___x_136_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_snd_127_, v___x_131_);
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_135_);
v___x_138_ = l_List_reverse___redArg(v___x_137_);
v___x_139_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3));
v___x_140_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(v___x_138_, v___x_139_);
v___x_141_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6);
v___x_142_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7));
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_140_);
v___x_144_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8));
v___x_145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_141_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = 0;
v___x_148_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*1, v___x_147_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_dec(v_x_151_);
return v_x_152_;
}
else
{
lean_object* v_head_154_; lean_object* v_tail_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_165_; 
v_head_154_ = lean_ctor_get(v_x_153_, 0);
v_tail_155_ = lean_ctor_get(v_x_153_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_165_ == 0)
{
v___x_157_ = v_x_153_;
v_isShared_158_ = v_isSharedCheck_165_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_tail_155_);
lean_inc(v_head_154_);
lean_dec(v_x_153_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_165_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
lean_inc(v_x_151_);
if (v_isShared_158_ == 0)
{
lean_ctor_set_tag(v___x_157_, 5);
lean_ctor_set(v___x_157_, 1, v_x_151_);
lean_ctor_set(v___x_157_, 0, v_x_152_);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_x_152_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_x_151_);
v___x_160_ = v_reuseFailAlloc_164_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_154_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v_x_152_ = v___x_162_;
v_x_153_ = v_tail_155_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
lean_dec(v_x_166_);
return v_x_167_;
}
else
{
lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_180_; 
v_head_169_ = lean_ctor_get(v_x_168_, 0);
v_tail_170_ = lean_ctor_get(v_x_168_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v_x_168_);
if (v_isSharedCheck_180_ == 0)
{
v___x_172_ = v_x_168_;
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_tail_170_);
lean_inc(v_head_169_);
lean_dec(v_x_168_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_180_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
lean_inc(v_x_166_);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 5);
lean_ctor_set(v___x_172_, 1, v_x_166_);
lean_ctor_set(v___x_172_, 0, v_x_167_);
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_x_167_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_x_166_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_169_);
v___x_177_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(v_x_166_, v___x_177_, v_tail_170_);
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_183_; 
lean_dec(v_x_182_);
v___x_183_ = lean_box(0);
return v___x_183_;
}
else
{
lean_object* v_tail_184_; 
v_tail_184_ = lean_ctor_get(v_x_181_, 1);
if (lean_obj_tag(v_tail_184_) == 0)
{
lean_object* v_head_185_; lean_object* v___x_186_; 
lean_dec(v_x_182_);
v_head_185_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_head_185_);
lean_dec_ref_known(v_x_181_, 2);
v___x_186_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_185_);
return v___x_186_;
}
else
{
lean_object* v_head_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v_tail_184_);
v_head_187_ = lean_ctor_get(v_x_181_, 0);
lean_inc(v_head_187_);
lean_dec_ref_known(v_x_181_, 2);
v___x_188_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_187_);
v___x_189_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(v_x_182_, v___x_188_, v_tail_184_);
return v___x_189_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0));
v___x_193_ = lean_string_length(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(lean_object* v_xs_203_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = lean_array_get_size(v_xs_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_207_ = lean_array_to_list(v_xs_203_);
v___x_208_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3));
v___x_209_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(v___x_207_, v___x_208_);
v___x_210_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3);
v___x_211_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4));
v___x_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_209_);
v___x_213_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5));
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_210_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = l_Std_Format_fill(v___x_215_);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
lean_dec_ref(v_xs_203_);
v___x_217_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7));
return v___x_217_;
}
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(2u);
v___x_231_ = lean_nat_to_int(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(lean_object* v_x_246_, lean_object* v_prec_247_){
_start:
{
lean_object* v___y_249_; lean_object* v___y_256_; 
switch(lean_obj_tag(v_x_246_))
{
case 0:
{
lean_object* v_remaining_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_282_; 
v_remaining_262_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_282_ == 0)
{
v___x_264_ = v_x_246_;
v_isShared_265_ = v_isSharedCheck_282_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_remaining_262_);
lean_dec(v_x_246_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_282_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___y_267_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(1024u);
v___x_279_ = lean_nat_dec_le(v___x_278_, v_prec_247_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_267_ = v___x_280_;
goto v___jp_266_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_267_ = v___x_281_;
goto v___jp_266_;
}
v___jp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6));
v___x_269_ = l_Nat_reprFast(v_remaining_262_);
if (v_isShared_265_ == 0)
{
lean_ctor_set_tag(v___x_264_, 3);
lean_ctor_set(v___x_264_, 0, v___x_269_);
v___x_271_ = v___x_264_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_277_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_268_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
lean_inc(v___y_267_);
v___x_273_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_273_, 0, v___y_267_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = 0;
v___x_275_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v___x_274_);
v___x_276_ = l_Repr_addAppParen(v___x_275_, v_prec_247_);
return v___x_276_;
}
}
}
}
case 1:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_unsigned_to_nat(1024u);
v___x_284_ = lean_nat_dec_le(v___x_283_, v_prec_247_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_249_ = v___x_285_;
goto v___jp_248_;
}
else
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_249_ = v___x_286_;
goto v___jp_248_;
}
}
case 2:
{
lean_object* v_ext_287_; lean_object* v_remaining_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_312_; 
v_ext_287_ = lean_ctor_get(v_x_246_, 0);
v_remaining_288_ = lean_ctor_get(v_x_246_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_312_ == 0)
{
v___x_290_ = v_x_246_;
v_isShared_291_ = v_isSharedCheck_312_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_remaining_288_);
lean_inc(v_ext_287_);
lean_dec(v_x_246_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_312_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___y_293_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1024u);
v___x_309_ = lean_nat_dec_le(v___x_308_, v_prec_247_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_293_ = v___x_310_;
goto v___jp_292_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_293_ = v___x_311_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_294_ = lean_box(1);
v___x_295_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11));
v___x_296_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(v_ext_287_);
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 5);
lean_ctor_set(v___x_290_, 1, v___x_296_);
lean_ctor_set(v___x_290_, 0, v___x_295_);
v___x_298_ = v___x_290_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_307_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_294_);
v___x_300_ = l_Nat_reprFast(v_remaining_288_);
v___x_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_299_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
lean_inc(v___y_293_);
v___x_303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_303_, 0, v___y_293_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = 0;
v___x_305_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_304_);
v___x_306_ = l_Repr_addAppParen(v___x_305_, v_prec_247_);
return v___x_306_;
}
}
}
}
case 3:
{
lean_object* v_ext_313_; lean_object* v_count_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_338_; 
v_ext_313_ = lean_ctor_get(v_x_246_, 0);
v_count_314_ = lean_ctor_get(v_x_246_, 1);
v_isSharedCheck_338_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_338_ == 0)
{
v___x_316_ = v_x_246_;
v_isShared_317_ = v_isSharedCheck_338_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_count_314_);
lean_inc(v_ext_313_);
lean_dec(v_x_246_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_338_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___y_319_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(1024u);
v___x_335_ = lean_nat_dec_le(v___x_334_, v_prec_247_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_319_ = v___x_336_;
goto v___jp_318_;
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_319_ = v___x_337_;
goto v___jp_318_;
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_320_ = lean_box(1);
v___x_321_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__14));
v___x_322_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(v_ext_313_);
if (v_isShared_317_ == 0)
{
lean_ctor_set_tag(v___x_316_, 5);
lean_ctor_set(v___x_316_, 1, v___x_322_);
lean_ctor_set(v___x_316_, 0, v___x_321_);
v___x_324_ = v___x_316_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_333_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_320_);
v___x_326_ = l_Nat_reprFast(v_count_314_);
v___x_327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_325_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
lean_inc(v___y_319_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___y_319_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = 0;
v___x_331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_330_);
v___x_332_ = l_Repr_addAppParen(v___x_331_, v_prec_247_);
return v___x_332_;
}
}
}
}
default: 
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1024u);
v___x_340_ = lean_nat_dec_le(v___x_339_, v_prec_247_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_256_ = v___x_341_;
goto v___jp_255_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_256_ = v___x_342_;
goto v___jp_255_;
}
}
}
v___jp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_250_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1));
lean_inc(v___y_249_);
v___x_251_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_251_, 0, v___y_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = 0;
v___x_253_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*1, v___x_252_);
v___x_254_ = l_Repr_addAppParen(v___x_253_, v_prec_247_);
return v___x_254_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_257_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3));
lean_inc(v___y_256_);
v___x_258_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_258_, 0, v___y_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = 0;
v___x_260_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*1, v___x_259_);
v___x_261_ = l_Repr_addAppParen(v___x_260_, v_prec_247_);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed(lean_object* v_x_343_, lean_object* v_prec_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_x_343_, v_prec_344_);
lean_dec(v_prec_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_nat_to_int(v_a_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(v_x_351_, v_x_352_);
lean_dec(v_x_352_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_356_) == 0)
{
if (lean_obj_tag(v_x_357_) == 0)
{
uint8_t v___x_358_; 
v___x_358_ = 1;
return v___x_358_;
}
else
{
uint8_t v___x_359_; 
v___x_359_ = 0;
return v___x_359_;
}
}
else
{
if (lean_obj_tag(v_x_357_) == 0)
{
uint8_t v___x_360_; 
v___x_360_ = 0;
return v___x_360_;
}
else
{
lean_object* v_val_361_; lean_object* v_val_362_; uint8_t v___x_363_; 
v_val_361_ = lean_ctor_get(v_x_356_, 0);
v_val_362_ = lean_ctor_get(v_x_357_, 0);
v___x_363_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_val_361_, v_val_362_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_x_364_, v_x_365_);
lean_dec(v_x_365_);
lean_dec(v_x_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(lean_object* v_xs_368_, lean_object* v_ys_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_zero_371_; uint8_t v_isZero_372_; 
v_zero_371_ = lean_unsigned_to_nat(0u);
v_isZero_372_ = lean_nat_dec_eq(v_x_370_, v_zero_371_);
if (v_isZero_372_ == 1)
{
lean_dec(v_x_370_);
return v_isZero_372_;
}
else
{
lean_object* v_one_373_; lean_object* v_n_374_; lean_object* v___x_375_; lean_object* v_fst_376_; lean_object* v_snd_377_; lean_object* v___x_378_; lean_object* v_fst_379_; lean_object* v_snd_380_; uint8_t v___x_381_; 
v_one_373_ = lean_unsigned_to_nat(1u);
v_n_374_ = lean_nat_sub(v_x_370_, v_one_373_);
lean_dec(v_x_370_);
v___x_375_ = lean_array_fget_borrowed(v_xs_368_, v_n_374_);
v_fst_376_ = lean_ctor_get(v___x_375_, 0);
v_snd_377_ = lean_ctor_get(v___x_375_, 1);
v___x_378_ = lean_array_fget_borrowed(v_ys_369_, v_n_374_);
v_fst_379_ = lean_ctor_get(v___x_378_, 0);
v_snd_380_ = lean_ctor_get(v___x_378_, 1);
v___x_381_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_fst_376_, v_fst_379_);
if (v___x_381_ == 0)
{
lean_dec(v_n_374_);
return v___x_381_;
}
else
{
uint8_t v___x_382_; 
v___x_382_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_snd_377_, v_snd_380_);
if (v___x_382_ == 0)
{
lean_dec(v_n_374_);
return v___x_382_;
}
else
{
v_x_370_ = v_n_374_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object* v_xs_384_, lean_object* v_ys_385_, lean_object* v_x_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_384_, v_ys_385_, v_x_386_);
lean_dec_ref(v_ys_385_);
lean_dec_ref(v_xs_384_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
lean_object* v_a_392_; lean_object* v_a_393_; lean_object* v_b_394_; lean_object* v_b_395_; 
switch(lean_obj_tag(v_x_389_))
{
case 0:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_remaining_401_; lean_object* v_remaining_402_; uint8_t v___x_403_; 
v_remaining_401_ = lean_ctor_get(v_x_389_, 0);
v_remaining_402_ = lean_ctor_get(v_x_390_, 0);
v___x_403_ = lean_nat_dec_eq(v_remaining_401_, v_remaining_402_);
return v___x_403_;
}
else
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
}
case 1:
{
if (lean_obj_tag(v_x_390_) == 1)
{
uint8_t v___x_405_; 
v___x_405_ = 1;
return v___x_405_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = 0;
return v___x_406_;
}
}
case 2:
{
if (lean_obj_tag(v_x_390_) == 2)
{
lean_object* v_ext_407_; lean_object* v_remaining_408_; lean_object* v_ext_409_; lean_object* v_remaining_410_; 
v_ext_407_ = lean_ctor_get(v_x_389_, 0);
v_remaining_408_ = lean_ctor_get(v_x_389_, 1);
v_ext_409_ = lean_ctor_get(v_x_390_, 0);
v_remaining_410_ = lean_ctor_get(v_x_390_, 1);
v_a_392_ = v_ext_407_;
v_a_393_ = v_remaining_408_;
v_b_394_ = v_ext_409_;
v_b_395_ = v_remaining_410_;
goto v___jp_391_;
}
else
{
uint8_t v___x_411_; 
v___x_411_ = 0;
return v___x_411_;
}
}
case 3:
{
if (lean_obj_tag(v_x_390_) == 3)
{
lean_object* v_ext_412_; lean_object* v_count_413_; lean_object* v_ext_414_; lean_object* v_count_415_; 
v_ext_412_ = lean_ctor_get(v_x_389_, 0);
v_count_413_ = lean_ctor_get(v_x_389_, 1);
v_ext_414_ = lean_ctor_get(v_x_390_, 0);
v_count_415_ = lean_ctor_get(v_x_390_, 1);
v_a_392_ = v_ext_412_;
v_a_393_ = v_count_413_;
v_b_394_ = v_ext_414_;
v_b_395_ = v_count_415_;
goto v___jp_391_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
}
default: 
{
if (lean_obj_tag(v_x_390_) == 4)
{
uint8_t v___x_417_; 
v___x_417_ = 1;
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
}
v___jp_391_:
{
lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_396_ = lean_array_get_size(v_a_392_);
v___x_397_ = lean_array_get_size(v_b_394_);
v___x_398_ = lean_nat_dec_eq(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_a_392_, v_b_394_, v___x_396_);
if (v___x_399_ == 0)
{
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_eq(v_a_393_, v_b_395_);
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_419_, v_x_420_);
lean_dec(v_x_420_);
lean_dec(v_x_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object* v_xs_423_, lean_object* v_ys_424_, lean_object* v_hsz_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_423_, v_ys_424_, v_x_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object* v_xs_429_, lean_object* v_ys_430_, lean_object* v_hsz_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(v_xs_429_, v_ys_430_, v_hsz_431_, v_x_432_, v_x_433_);
lean_dec_ref(v_ys_430_);
lean_dec_ref(v_xs_429_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_obj_tag_nat(v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg___boxed(lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(v_x_440_);
lean_dec(v_x_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(uint8_t v_dir_442_, lean_object* v_x_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_tag_nat(v_x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___boxed(lean_object* v_dir_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_dir_boxed_447_; lean_object* v_res_448_; 
v_dir_boxed_447_ = lean_unbox(v_dir_445_);
v_res_448_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(v_dir_boxed_447_, v_x_446_);
lean_dec(v_x_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(lean_object* v_t_449_, lean_object* v_k_450_){
_start:
{
switch(lean_obj_tag(v_t_449_))
{
case 1:
{
lean_object* v_a_451_; lean_object* v___x_452_; 
v_a_451_ = lean_ctor_get(v_t_449_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v_t_449_, 1);
v___x_452_ = lean_apply_1(v_k_450_, v_a_451_);
return v___x_452_;
}
case 2:
{
lean_object* v_a_453_; lean_object* v___x_454_; 
v_a_453_ = lean_ctor_get(v_t_449_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v_t_449_, 1);
v___x_454_ = lean_apply_1(v_k_450_, v_a_453_);
return v___x_454_;
}
case 3:
{
lean_object* v_a_455_; lean_object* v___x_456_; 
v_a_455_ = lean_ctor_get(v_t_449_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v_t_449_, 1);
v___x_456_ = lean_apply_1(v_k_450_, v_a_455_);
return v___x_456_;
}
case 7:
{
lean_object* v_error_457_; lean_object* v___x_458_; 
v_error_457_ = lean_ctor_get(v_t_449_, 0);
lean_inc(v_error_457_);
lean_dec_ref_known(v_t_449_, 1);
v___x_458_ = lean_apply_1(v_k_450_, v_error_457_);
return v___x_458_;
}
default: 
{
lean_dec(v_t_449_);
return v_k_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t v_dir_459_, lean_object* v_motive_460_, lean_object* v_ctorIdx_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_k_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_462_, v_k_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object* v_dir_466_, lean_object* v_motive_467_, lean_object* v_ctorIdx_468_, lean_object* v_t_469_, lean_object* v_h_470_, lean_object* v_k_471_){
_start:
{
uint8_t v_dir_boxed_472_; lean_object* v_res_473_; 
v_dir_boxed_472_ = lean_unbox(v_dir_466_);
v_res_473_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_boxed_472_, v_motive_467_, v_ctorIdx_468_, v_t_469_, v_h_470_, v_k_471_);
lean_dec(v_ctorIdx_468_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object* v_t_474_, lean_object* v_needStartLine_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_474_, v_needStartLine_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t v_dir_477_, lean_object* v_motive_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_needStartLine_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_479_, v_needStartLine_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object* v_dir_483_, lean_object* v_motive_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_needStartLine_487_){
_start:
{
uint8_t v_dir_boxed_488_; lean_object* v_res_489_; 
v_dir_boxed_488_ = lean_unbox(v_dir_483_);
v_res_489_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_boxed_488_, v_motive_484_, v_t_485_, v_h_486_, v_needStartLine_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object* v_t_490_, lean_object* v_needHeader_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_490_, v_needHeader_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t v_dir_493_, lean_object* v_motive_494_, lean_object* v_t_495_, lean_object* v_h_496_, lean_object* v_needHeader_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_495_, v_needHeader_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object* v_dir_499_, lean_object* v_motive_500_, lean_object* v_t_501_, lean_object* v_h_502_, lean_object* v_needHeader_503_){
_start:
{
uint8_t v_dir_boxed_504_; lean_object* v_res_505_; 
v_dir_boxed_504_ = lean_unbox(v_dir_499_);
v_res_505_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_boxed_504_, v_motive_500_, v_t_501_, v_h_502_, v_needHeader_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object* v_t_506_, lean_object* v_readBody_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_506_, v_readBody_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t v_dir_509_, lean_object* v_motive_510_, lean_object* v_t_511_, lean_object* v_h_512_, lean_object* v_readBody_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_511_, v_readBody_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object* v_dir_515_, lean_object* v_motive_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_readBody_519_){
_start:
{
uint8_t v_dir_boxed_520_; lean_object* v_res_521_; 
v_dir_boxed_520_ = lean_unbox(v_dir_515_);
v_res_521_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_boxed_520_, v_motive_516_, v_t_517_, v_h_518_, v_readBody_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object* v_t_522_, lean_object* v_continue_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_522_, v_continue_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t v_dir_525_, lean_object* v_motive_526_, lean_object* v_t_527_, lean_object* v_h_528_, lean_object* v_continue_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_527_, v_continue_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(lean_object* v_dir_531_, lean_object* v_motive_532_, lean_object* v_t_533_, lean_object* v_h_534_, lean_object* v_continue_535_){
_start:
{
uint8_t v_dir_boxed_536_; lean_object* v_res_537_; 
v_dir_boxed_536_ = lean_unbox(v_dir_531_);
v_res_537_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(v_dir_boxed_536_, v_motive_532_, v_t_533_, v_h_534_, v_continue_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(lean_object* v_t_538_, lean_object* v_pending_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_538_, v_pending_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t v_dir_541_, lean_object* v_motive_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_pending_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_543_, v_pending_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object* v_dir_547_, lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_pending_551_){
_start:
{
uint8_t v_dir_boxed_552_; lean_object* v_res_553_; 
v_dir_boxed_552_ = lean_unbox(v_dir_547_);
v_res_553_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_boxed_552_, v_motive_548_, v_t_549_, v_h_550_, v_pending_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object* v_t_554_, lean_object* v_complete_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_554_, v_complete_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t v_dir_557_, lean_object* v_motive_558_, lean_object* v_t_559_, lean_object* v_h_560_, lean_object* v_complete_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_559_, v_complete_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object* v_dir_563_, lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_complete_567_){
_start:
{
uint8_t v_dir_boxed_568_; lean_object* v_res_569_; 
v_dir_boxed_568_ = lean_unbox(v_dir_563_);
v_res_569_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_boxed_568_, v_motive_564_, v_t_565_, v_h_566_, v_complete_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object* v_t_570_, lean_object* v_closed_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_570_, v_closed_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t v_dir_573_, lean_object* v_motive_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_closed_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_575_, v_closed_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object* v_dir_579_, lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_closed_583_){
_start:
{
uint8_t v_dir_boxed_584_; lean_object* v_res_585_; 
v_dir_boxed_584_ = lean_unbox(v_dir_579_);
v_res_585_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_boxed_584_, v_motive_580_, v_t_581_, v_h_582_, v_closed_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(lean_object* v_t_586_, lean_object* v_failed_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_586_, v_failed_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim(uint8_t v_dir_589_, lean_object* v_motive_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_failed_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_591_, v_failed_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(lean_object* v_dir_595_, lean_object* v_motive_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_failed_599_){
_start:
{
uint8_t v_dir_boxed_600_; lean_object* v_res_601_; 
v_dir_boxed_600_ = lean_unbox(v_dir_595_);
v_res_601_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(v_dir_boxed_600_, v_motive_596_, v_t_597_, v_h_598_, v_failed_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg(){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(0);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object* v___dummy_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_box(0);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_608_){
_start:
{
uint8_t v_dir_boxed_609_; lean_object* v_res_610_; 
v_dir_boxed_609_ = lean_unbox(v_dir_608_);
v_res_610_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg(){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object* v___dummy_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_box(0);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_617_){
_start:
{
uint8_t v_a_11__boxed_618_; lean_object* v_res_619_; 
v_a_11__boxed_618_ = lean_unbox(v_a_617_);
v_res_619_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_11__boxed_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_656_, lean_object* v_prec_657_){
_start:
{
lean_object* v___y_659_; lean_object* v___y_666_; lean_object* v___y_673_; lean_object* v___y_680_; 
switch(lean_obj_tag(v_x_656_))
{
case 0:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(1024u);
v___x_687_ = lean_nat_dec_le(v___x_686_, v_prec_657_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_680_ = v___x_688_;
goto v___jp_679_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_680_ = v___x_689_;
goto v___jp_679_;
}
}
case 1:
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_710_; 
v_a_690_ = lean_ctor_get(v_x_656_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_710_ == 0)
{
v___x_692_ = v_x_656_;
v_isShared_693_ = v_isSharedCheck_710_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v_x_656_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_710_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___y_695_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(1024u);
v___x_707_ = lean_nat_dec_le(v___x_706_, v_prec_657_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_695_ = v___x_708_;
goto v___jp_694_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_695_ = v___x_709_;
goto v___jp_694_;
}
v___jp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_696_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_697_ = l_Nat_reprFast(v_a_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set_tag(v___x_692_, 3);
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_705_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_696_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
lean_inc(v___y_695_);
v___x_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_701_, 0, v___y_695_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = 0;
v___x_703_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*1, v___x_702_);
v___x_704_ = l_Repr_addAppParen(v___x_703_, v_prec_657_);
return v___x_704_;
}
}
}
}
case 2:
{
lean_object* v_a_711_; lean_object* v___y_713_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_a_711_ = lean_ctor_get(v_x_656_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v_x_656_, 1);
v___x_722_ = lean_unsigned_to_nat(1024u);
v___x_723_ = lean_nat_dec_le(v___x_722_, v_prec_657_);
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
v___x_714_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_715_ = lean_unsigned_to_nat(1024u);
v___x_716_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_711_, v___x_715_);
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
v___x_721_ = l_Repr_addAppParen(v___x_720_, v_prec_657_);
return v___x_721_;
}
}
case 3:
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___y_729_; uint8_t v___x_737_; 
v_a_726_ = lean_ctor_get(v_x_656_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v_x_656_, 1);
v___x_727_ = lean_unsigned_to_nat(1024u);
v___x_737_ = lean_nat_dec_le(v___x_727_, v_prec_657_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_729_ = v___x_738_;
goto v___jp_728_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_729_ = v___x_739_;
goto v___jp_728_;
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_730_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_731_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_726_, v___x_727_);
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
lean_inc(v___y_729_);
v___x_733_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_733_, 0, v___y_729_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = 0;
v___x_735_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set_uint8(v___x_735_, sizeof(void*)*1, v___x_734_);
v___x_736_ = l_Repr_addAppParen(v___x_735_, v_prec_657_);
return v___x_736_;
}
}
case 4:
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(1024u);
v___x_741_ = lean_nat_dec_le(v___x_740_, v_prec_657_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
v___x_742_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_673_ = v___x_742_;
goto v___jp_672_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_673_ = v___x_743_;
goto v___jp_672_;
}
}
case 5:
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(1024u);
v___x_745_ = lean_nat_dec_le(v___x_744_, v_prec_657_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_666_ = v___x_746_;
goto v___jp_665_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_666_ = v___x_747_;
goto v___jp_665_;
}
}
case 6:
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(1024u);
v___x_749_ = lean_nat_dec_le(v___x_748_, v_prec_657_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; 
v___x_750_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_659_ = v___x_750_;
goto v___jp_658_;
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_659_ = v___x_751_;
goto v___jp_658_;
}
}
default: 
{
lean_object* v_error_752_; lean_object* v___y_754_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_error_752_ = lean_ctor_get(v_x_656_, 0);
lean_inc(v_error_752_);
lean_dec_ref_known(v_x_656_, 1);
v___x_763_ = lean_unsigned_to_nat(1024u);
v___x_764_ = lean_nat_dec_le(v___x_763_, v_prec_657_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_754_ = v___x_765_;
goto v___jp_753_;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_754_ = v___x_766_;
goto v___jp_753_;
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_755_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19));
v___x_756_ = lean_unsigned_to_nat(1024u);
v___x_757_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_752_, v___x_756_);
v___x_758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_755_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
lean_inc(v___y_754_);
v___x_759_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_759_, 0, v___y_754_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = 0;
v___x_761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set_uint8(v___x_761_, sizeof(void*)*1, v___x_760_);
v___x_762_ = l_Repr_addAppParen(v___x_761_, v_prec_657_);
return v___x_762_;
}
}
}
v___jp_658_:
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_660_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_659_);
v___x_661_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_661_, 0, v___y_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = 0;
v___x_663_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set_uint8(v___x_663_, sizeof(void*)*1, v___x_662_);
v___x_664_ = l_Repr_addAppParen(v___x_663_, v_prec_657_);
return v___x_664_;
}
v___jp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_666_);
v___x_668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_668_, 0, v___y_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = 0;
v___x_670_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*1, v___x_669_);
v___x_671_ = l_Repr_addAppParen(v___x_670_, v_prec_657_);
return v___x_671_;
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_674_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_673_);
v___x_675_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_675_, 0, v___y_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = 0;
v___x_677_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set_uint8(v___x_677_, sizeof(void*)*1, v___x_676_);
v___x_678_ = l_Repr_addAppParen(v___x_677_, v_prec_657_);
return v___x_678_;
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_681_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_680_);
v___x_682_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_682_, 0, v___y_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = 0;
v___x_684_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*1, v___x_683_);
v___x_685_ = l_Repr_addAppParen(v___x_684_, v_prec_657_);
return v___x_685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_767_, lean_object* v_prec_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_767_, v_prec_768_);
lean_dec(v_prec_768_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_770_, lean_object* v_x_771_, lean_object* v_prec_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_771_, v_prec_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_774_, lean_object* v_x_775_, lean_object* v_prec_776_){
_start:
{
uint8_t v_dir_876__boxed_777_; lean_object* v_res_778_; 
v_dir_876__boxed_777_ = lean_unbox(v_dir_774_);
v_res_778_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_876__boxed_777_, v_x_775_, v_prec_776_);
lean_dec(v_prec_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(v_dir_779_);
v___x_781_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_782_){
_start:
{
uint8_t v_dir_5__boxed_783_; lean_object* v_res_784_; 
v_dir_5__boxed_783_ = lean_unbox(v_dir_782_);
v_res_784_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_783_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_785_, lean_object* v_x_786_){
_start:
{
switch(lean_obj_tag(v_x_785_))
{
case 0:
{
if (lean_obj_tag(v_x_786_) == 0)
{
uint8_t v___x_787_; 
v___x_787_ = 1;
return v___x_787_;
}
else
{
uint8_t v___x_788_; 
v___x_788_ = 0;
return v___x_788_;
}
}
case 1:
{
if (lean_obj_tag(v_x_786_) == 1)
{
lean_object* v_a_789_; lean_object* v_a_790_; uint8_t v___x_791_; 
v_a_789_ = lean_ctor_get(v_x_785_, 0);
v_a_790_ = lean_ctor_get(v_x_786_, 0);
v___x_791_ = lean_nat_dec_eq(v_a_789_, v_a_790_);
return v___x_791_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = 0;
return v___x_792_;
}
}
case 2:
{
if (lean_obj_tag(v_x_786_) == 2)
{
lean_object* v_a_793_; lean_object* v_a_794_; uint8_t v___x_795_; 
v_a_793_ = lean_ctor_get(v_x_785_, 0);
v_a_794_ = lean_ctor_get(v_x_786_, 0);
v___x_795_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_793_, v_a_794_);
return v___x_795_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = 0;
return v___x_796_;
}
}
case 3:
{
if (lean_obj_tag(v_x_786_) == 3)
{
lean_object* v_a_797_; lean_object* v_a_798_; 
v_a_797_ = lean_ctor_get(v_x_785_, 0);
v_a_798_ = lean_ctor_get(v_x_786_, 0);
v_x_785_ = v_a_797_;
v_x_786_ = v_a_798_;
goto _start;
}
else
{
uint8_t v___x_800_; 
v___x_800_ = 0;
return v___x_800_;
}
}
case 4:
{
if (lean_obj_tag(v_x_786_) == 4)
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
case 5:
{
if (lean_obj_tag(v_x_786_) == 5)
{
uint8_t v___x_803_; 
v___x_803_ = 1;
return v___x_803_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
}
case 6:
{
if (lean_obj_tag(v_x_786_) == 6)
{
uint8_t v___x_805_; 
v___x_805_ = 1;
return v___x_805_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = 0;
return v___x_806_;
}
}
default: 
{
if (lean_obj_tag(v_x_786_) == 7)
{
lean_object* v_error_807_; lean_object* v_error_808_; uint8_t v___x_809_; 
v_error_807_ = lean_ctor_get(v_x_785_, 0);
v_error_808_ = lean_ctor_get(v_x_786_, 0);
v___x_809_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_error_807_, v_error_808_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec(v_x_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_815_, lean_object* v_x_816_, lean_object* v_x_817_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_816_, v_x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_819_, lean_object* v_x_820_, lean_object* v_x_821_){
_start:
{
uint8_t v_dir_183__boxed_822_; uint8_t v_res_823_; lean_object* v_r_824_; 
v_dir_183__boxed_822_ = lean_unbox(v_dir_819_);
v_res_823_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_183__boxed_822_, v_x_820_, v_x_821_);
lean_dec(v_x_821_);
lean_dec(v_x_820_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_box(v_dir_825_);
v___x_827_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_828_){
_start:
{
uint8_t v_dir_5__boxed_829_; lean_object* v_res_830_; 
v_dir_5__boxed_829_ = lean_unbox(v_dir_828_);
v_res_830_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_829_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_831_){
_start:
{
lean_object* v_state_832_; 
v_state_832_ = lean_ctor_get(v_reader_831_, 0);
if (lean_obj_tag(v_state_832_) == 6)
{
uint8_t v___x_833_; 
v___x_833_ = 1;
return v___x_833_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = 0;
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_835_);
lean_dec_ref(v_reader_835_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_838_, lean_object* v_reader_839_){
_start:
{
lean_object* v_state_840_; 
v_state_840_ = lean_ctor_get(v_reader_839_, 0);
if (lean_obj_tag(v_state_840_) == 6)
{
uint8_t v___x_841_; 
v___x_841_ = 1;
return v___x_841_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = 0;
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_843_, lean_object* v_reader_844_){
_start:
{
uint8_t v_dir_boxed_845_; uint8_t v_res_846_; lean_object* v_r_847_; 
v_dir_boxed_845_ = lean_unbox(v_dir_843_);
v_res_846_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_845_, v_reader_844_);
lean_dec_ref(v_reader_844_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_848_){
_start:
{
lean_object* v_state_849_; 
v_state_849_ = lean_ctor_get(v_reader_848_, 0);
if (lean_obj_tag(v_state_849_) == 5)
{
uint8_t v___x_850_; 
v___x_850_ = 1;
return v___x_850_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = 0;
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_852_){
_start:
{
uint8_t v_res_853_; lean_object* v_r_854_; 
v_res_853_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_852_);
lean_dec_ref(v_reader_852_);
v_r_854_ = lean_box(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_855_, lean_object* v_reader_856_){
_start:
{
lean_object* v_state_857_; 
v_state_857_ = lean_ctor_get(v_reader_856_, 0);
if (lean_obj_tag(v_state_857_) == 5)
{
uint8_t v___x_858_; 
v___x_858_ = 1;
return v___x_858_;
}
else
{
uint8_t v___x_859_; 
v___x_859_ = 0;
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_860_, lean_object* v_reader_861_){
_start:
{
uint8_t v_dir_boxed_862_; uint8_t v_res_863_; lean_object* v_r_864_; 
v_dir_boxed_862_ = lean_unbox(v_dir_860_);
v_res_863_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_862_, v_reader_861_);
lean_dec_ref(v_reader_861_);
v_r_864_ = lean_box(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object* v_reader_865_){
_start:
{
lean_object* v_state_866_; 
v_state_866_ = lean_ctor_get(v_reader_865_, 0);
if (lean_obj_tag(v_state_866_) == 7)
{
uint8_t v___x_867_; 
v___x_867_ = 1;
return v___x_867_;
}
else
{
uint8_t v___x_868_; 
v___x_868_ = 0;
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object* v_reader_869_){
_start:
{
uint8_t v_res_870_; lean_object* v_r_871_; 
v_res_870_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_869_);
lean_dec_ref(v_reader_869_);
v_r_871_ = lean_box(v_res_870_);
return v_r_871_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t v_dir_872_, lean_object* v_reader_873_){
_start:
{
lean_object* v_state_874_; 
v_state_874_ = lean_ctor_get(v_reader_873_, 0);
if (lean_obj_tag(v_state_874_) == 7)
{
uint8_t v___x_875_; 
v___x_875_ = 1;
return v___x_875_;
}
else
{
uint8_t v___x_876_; 
v___x_876_ = 0;
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object* v_dir_877_, lean_object* v_reader_878_){
_start:
{
uint8_t v_dir_boxed_879_; uint8_t v_res_880_; lean_object* v_r_881_; 
v_dir_boxed_879_ = lean_unbox(v_dir_877_);
v_res_880_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_879_, v_reader_878_);
lean_dec_ref(v_reader_878_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_882_, lean_object* v_reader_883_){
_start:
{
lean_object* v_input_884_; lean_object* v_state_885_; lean_object* v_messageHead_886_; lean_object* v_messageCount_887_; lean_object* v_bodyBytesRead_888_; lean_object* v_headerBytesRead_889_; uint8_t v_noMoreInput_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_911_; 
v_input_884_ = lean_ctor_get(v_reader_883_, 1);
v_state_885_ = lean_ctor_get(v_reader_883_, 0);
v_messageHead_886_ = lean_ctor_get(v_reader_883_, 2);
v_messageCount_887_ = lean_ctor_get(v_reader_883_, 3);
v_bodyBytesRead_888_ = lean_ctor_get(v_reader_883_, 4);
v_headerBytesRead_889_ = lean_ctor_get(v_reader_883_, 5);
v_noMoreInput_890_ = lean_ctor_get_uint8(v_reader_883_, sizeof(void*)*6);
v_isSharedCheck_911_ = !lean_is_exclusive(v_reader_883_);
if (v_isSharedCheck_911_ == 0)
{
v___x_892_ = v_reader_883_;
v_isShared_893_ = v_isSharedCheck_911_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_headerBytesRead_889_);
lean_inc(v_bodyBytesRead_888_);
lean_inc(v_messageCount_887_);
lean_inc(v_messageHead_886_);
lean_inc(v_input_884_);
lean_inc(v_state_885_);
lean_dec(v_reader_883_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_911_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_array_894_; lean_object* v_idx_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_array_894_ = lean_ctor_get(v_input_884_, 0);
lean_inc_ref(v_array_894_);
v_idx_895_ = lean_ctor_get(v_input_884_, 1);
lean_inc(v_idx_895_);
lean_dec_ref(v_input_884_);
v___x_896_ = lean_byte_array_size(v_array_894_);
v___x_897_ = lean_nat_dec_le(v___x_896_, v_idx_895_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_898_ = l_ByteArray_extract(v_array_894_, v_idx_895_, v___x_896_);
lean_dec_ref(v_array_894_);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_byte_array_size(v___x_898_);
v___x_901_ = lean_byte_array_size(v_data_882_);
v___x_902_ = lean_byte_array_copy_slice(v_data_882_, v___x_899_, v___x_898_, v___x_900_, v___x_901_, v___x_897_);
lean_dec_ref(v_data_882_);
v___x_903_ = l_ByteArray_mkIterator(v___x_902_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___x_903_);
v___x_905_ = v___x_892_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_state_885_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_messageHead_886_);
lean_ctor_set(v_reuseFailAlloc_906_, 3, v_messageCount_887_);
lean_ctor_set(v_reuseFailAlloc_906_, 4, v_bodyBytesRead_888_);
lean_ctor_set(v_reuseFailAlloc_906_, 5, v_headerBytesRead_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_906_, sizeof(void*)*6, v_noMoreInput_890_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v_idx_895_);
lean_dec_ref(v_array_894_);
v___x_907_ = l_ByteArray_mkIterator(v_data_882_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___x_907_);
v___x_909_ = v___x_892_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_state_885_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_messageHead_886_);
lean_ctor_set(v_reuseFailAlloc_910_, 3, v_messageCount_887_);
lean_ctor_set(v_reuseFailAlloc_910_, 4, v_bodyBytesRead_888_);
lean_ctor_set(v_reuseFailAlloc_910_, 5, v_headerBytesRead_889_);
lean_ctor_set_uint8(v_reuseFailAlloc_910_, sizeof(void*)*6, v_noMoreInput_890_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_912_, lean_object* v_data_913_, lean_object* v_reader_914_){
_start:
{
lean_object* v_input_915_; lean_object* v_state_916_; lean_object* v_messageHead_917_; lean_object* v_messageCount_918_; lean_object* v_bodyBytesRead_919_; lean_object* v_headerBytesRead_920_; uint8_t v_noMoreInput_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_942_; 
v_input_915_ = lean_ctor_get(v_reader_914_, 1);
v_state_916_ = lean_ctor_get(v_reader_914_, 0);
v_messageHead_917_ = lean_ctor_get(v_reader_914_, 2);
v_messageCount_918_ = lean_ctor_get(v_reader_914_, 3);
v_bodyBytesRead_919_ = lean_ctor_get(v_reader_914_, 4);
v_headerBytesRead_920_ = lean_ctor_get(v_reader_914_, 5);
v_noMoreInput_921_ = lean_ctor_get_uint8(v_reader_914_, sizeof(void*)*6);
v_isSharedCheck_942_ = !lean_is_exclusive(v_reader_914_);
if (v_isSharedCheck_942_ == 0)
{
v___x_923_ = v_reader_914_;
v_isShared_924_ = v_isSharedCheck_942_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_headerBytesRead_920_);
lean_inc(v_bodyBytesRead_919_);
lean_inc(v_messageCount_918_);
lean_inc(v_messageHead_917_);
lean_inc(v_input_915_);
lean_inc(v_state_916_);
lean_dec(v_reader_914_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_942_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_array_925_; lean_object* v_idx_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_array_925_ = lean_ctor_get(v_input_915_, 0);
lean_inc_ref(v_array_925_);
v_idx_926_ = lean_ctor_get(v_input_915_, 1);
lean_inc(v_idx_926_);
lean_dec_ref(v_input_915_);
v___x_927_ = lean_byte_array_size(v_array_925_);
v___x_928_ = lean_nat_dec_le(v___x_927_, v_idx_926_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_929_ = l_ByteArray_extract(v_array_925_, v_idx_926_, v___x_927_);
lean_dec_ref(v_array_925_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_byte_array_size(v___x_929_);
v___x_932_ = lean_byte_array_size(v_data_913_);
v___x_933_ = lean_byte_array_copy_slice(v_data_913_, v___x_930_, v___x_929_, v___x_931_, v___x_932_, v___x_928_);
lean_dec_ref(v_data_913_);
v___x_934_ = l_ByteArray_mkIterator(v___x_933_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___x_934_);
v___x_936_ = v___x_923_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_state_916_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_messageHead_917_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_messageCount_918_);
lean_ctor_set(v_reuseFailAlloc_937_, 4, v_bodyBytesRead_919_);
lean_ctor_set(v_reuseFailAlloc_937_, 5, v_headerBytesRead_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*6, v_noMoreInput_921_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_940_; 
lean_dec(v_idx_926_);
lean_dec_ref(v_array_925_);
v___x_938_ = l_ByteArray_mkIterator(v_data_913_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___x_938_);
v___x_940_ = v___x_923_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_state_916_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_messageHead_917_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_messageCount_918_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_bodyBytesRead_919_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v_headerBytesRead_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_941_, sizeof(void*)*6, v_noMoreInput_921_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_943_, lean_object* v_data_944_, lean_object* v_reader_945_){
_start:
{
uint8_t v_dir_boxed_946_; lean_object* v_res_947_; 
v_dir_boxed_946_ = lean_unbox(v_dir_943_);
v_res_947_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_946_, v_data_944_, v_reader_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_948_, lean_object* v_reader_949_){
_start:
{
lean_object* v_state_950_; lean_object* v_messageHead_951_; lean_object* v_messageCount_952_; lean_object* v_bodyBytesRead_953_; lean_object* v_headerBytesRead_954_; uint8_t v_noMoreInput_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_state_950_ = lean_ctor_get(v_reader_949_, 0);
v_messageHead_951_ = lean_ctor_get(v_reader_949_, 2);
v_messageCount_952_ = lean_ctor_get(v_reader_949_, 3);
v_bodyBytesRead_953_ = lean_ctor_get(v_reader_949_, 4);
v_headerBytesRead_954_ = lean_ctor_get(v_reader_949_, 5);
v_noMoreInput_955_ = lean_ctor_get_uint8(v_reader_949_, sizeof(void*)*6);
v_isSharedCheck_962_ = !lean_is_exclusive(v_reader_949_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_reader_949_, 1);
lean_dec(v_unused_963_);
v___x_957_ = v_reader_949_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_headerBytesRead_954_);
lean_inc(v_bodyBytesRead_953_);
lean_inc(v_messageCount_952_);
lean_inc(v_messageHead_951_);
lean_inc(v_state_950_);
lean_dec(v_reader_949_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_input_948_);
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_state_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_input_948_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_messageHead_951_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_messageCount_952_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_bodyBytesRead_953_);
lean_ctor_set(v_reuseFailAlloc_961_, 5, v_headerBytesRead_954_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*6, v_noMoreInput_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_964_, lean_object* v_input_965_, lean_object* v_reader_966_){
_start:
{
lean_object* v_state_967_; lean_object* v_messageHead_968_; lean_object* v_messageCount_969_; lean_object* v_bodyBytesRead_970_; lean_object* v_headerBytesRead_971_; uint8_t v_noMoreInput_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_state_967_ = lean_ctor_get(v_reader_966_, 0);
v_messageHead_968_ = lean_ctor_get(v_reader_966_, 2);
v_messageCount_969_ = lean_ctor_get(v_reader_966_, 3);
v_bodyBytesRead_970_ = lean_ctor_get(v_reader_966_, 4);
v_headerBytesRead_971_ = lean_ctor_get(v_reader_966_, 5);
v_noMoreInput_972_ = lean_ctor_get_uint8(v_reader_966_, sizeof(void*)*6);
v_isSharedCheck_979_ = !lean_is_exclusive(v_reader_966_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; 
v_unused_980_ = lean_ctor_get(v_reader_966_, 1);
lean_dec(v_unused_980_);
v___x_974_ = v_reader_966_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_headerBytesRead_971_);
lean_inc(v_bodyBytesRead_970_);
lean_inc(v_messageCount_969_);
lean_inc(v_messageHead_968_);
lean_inc(v_state_967_);
lean_dec(v_reader_966_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_input_965_);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_state_967_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_input_965_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_messageHead_968_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_messageCount_969_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_bodyBytesRead_970_);
lean_ctor_set(v_reuseFailAlloc_978_, 5, v_headerBytesRead_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*6, v_noMoreInput_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object* v_dir_981_, lean_object* v_input_982_, lean_object* v_reader_983_){
_start:
{
uint8_t v_dir_boxed_984_; lean_object* v_res_985_; 
v_dir_boxed_984_ = lean_unbox(v_dir_981_);
v_res_985_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_984_, v_input_982_, v_reader_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object* v_messageHead_986_, lean_object* v_reader_987_){
_start:
{
lean_object* v_state_988_; lean_object* v_input_989_; lean_object* v_messageCount_990_; lean_object* v_bodyBytesRead_991_; lean_object* v_headerBytesRead_992_; uint8_t v_noMoreInput_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_state_988_ = lean_ctor_get(v_reader_987_, 0);
v_input_989_ = lean_ctor_get(v_reader_987_, 1);
v_messageCount_990_ = lean_ctor_get(v_reader_987_, 3);
v_bodyBytesRead_991_ = lean_ctor_get(v_reader_987_, 4);
v_headerBytesRead_992_ = lean_ctor_get(v_reader_987_, 5);
v_noMoreInput_993_ = lean_ctor_get_uint8(v_reader_987_, sizeof(void*)*6);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_reader_987_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v_reader_987_, 2);
lean_dec(v_unused_1001_);
v___x_995_ = v_reader_987_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_headerBytesRead_992_);
lean_inc(v_bodyBytesRead_991_);
lean_inc(v_messageCount_990_);
lean_inc(v_input_989_);
lean_inc(v_state_988_);
lean_dec(v_reader_987_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 2, v_messageHead_986_);
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_state_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_input_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_messageHead_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_messageCount_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_bodyBytesRead_991_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_headerBytesRead_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*6, v_noMoreInput_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_1002_, lean_object* v_messageHead_1003_, lean_object* v_reader_1004_){
_start:
{
lean_object* v_state_1005_; lean_object* v_input_1006_; lean_object* v_messageCount_1007_; lean_object* v_bodyBytesRead_1008_; lean_object* v_headerBytesRead_1009_; uint8_t v_noMoreInput_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_state_1005_ = lean_ctor_get(v_reader_1004_, 0);
v_input_1006_ = lean_ctor_get(v_reader_1004_, 1);
v_messageCount_1007_ = lean_ctor_get(v_reader_1004_, 3);
v_bodyBytesRead_1008_ = lean_ctor_get(v_reader_1004_, 4);
v_headerBytesRead_1009_ = lean_ctor_get(v_reader_1004_, 5);
v_noMoreInput_1010_ = lean_ctor_get_uint8(v_reader_1004_, sizeof(void*)*6);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_reader_1004_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v_reader_1004_, 2);
lean_dec(v_unused_1018_);
v___x_1012_ = v_reader_1004_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_headerBytesRead_1009_);
lean_inc(v_bodyBytesRead_1008_);
lean_inc(v_messageCount_1007_);
lean_inc(v_input_1006_);
lean_inc(v_state_1005_);
lean_dec(v_reader_1004_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 2, v_messageHead_1003_);
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_state_1005_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_input_1006_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_messageHead_1003_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_messageCount_1007_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v_bodyBytesRead_1008_);
lean_ctor_set(v_reuseFailAlloc_1016_, 5, v_headerBytesRead_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1016_, sizeof(void*)*6, v_noMoreInput_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_1019_, lean_object* v_messageHead_1020_, lean_object* v_reader_1021_){
_start:
{
uint8_t v_dir_boxed_1022_; lean_object* v_res_1023_; 
v_dir_boxed_1022_ = lean_unbox(v_dir_1019_);
v_res_1023_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_1022_, v_messageHead_1020_, v_reader_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_1024_, lean_object* v_name_1025_, lean_object* v_value_1026_, lean_object* v_reader_1027_){
_start:
{
if (v_dir_1024_ == 0)
{
lean_object* v_messageHead_1028_; lean_object* v_state_1029_; lean_object* v_input_1030_; lean_object* v_messageCount_1031_; lean_object* v_bodyBytesRead_1032_; lean_object* v_headerBytesRead_1033_; uint8_t v_noMoreInput_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1056_; 
v_messageHead_1028_ = lean_ctor_get(v_reader_1027_, 2);
v_state_1029_ = lean_ctor_get(v_reader_1027_, 0);
v_input_1030_ = lean_ctor_get(v_reader_1027_, 1);
v_messageCount_1031_ = lean_ctor_get(v_reader_1027_, 3);
v_bodyBytesRead_1032_ = lean_ctor_get(v_reader_1027_, 4);
v_headerBytesRead_1033_ = lean_ctor_get(v_reader_1027_, 5);
v_noMoreInput_1034_ = lean_ctor_get_uint8(v_reader_1027_, sizeof(void*)*6);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_reader_1027_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1036_ = v_reader_1027_;
v_isShared_1037_ = v_isSharedCheck_1056_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_headerBytesRead_1033_);
lean_inc(v_bodyBytesRead_1032_);
lean_inc(v_messageCount_1031_);
lean_inc(v_messageHead_1028_);
lean_inc(v_input_1030_);
lean_inc(v_state_1029_);
lean_dec(v_reader_1027_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1056_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v_method_1038_; uint8_t v_version_1039_; lean_object* v_uri_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1053_; 
v_method_1038_ = lean_ctor_get_uint8(v_messageHead_1028_, sizeof(void*)*2);
v_version_1039_ = lean_ctor_get_uint8(v_messageHead_1028_, sizeof(void*)*2 + 1);
v_uri_1040_ = lean_ctor_get(v_messageHead_1028_, 0);
lean_inc(v_uri_1040_);
v___x_1041_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1024_, v_messageHead_1028_);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_messageHead_1028_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1054_ = lean_ctor_get(v_messageHead_1028_, 1);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_messageHead_1028_, 0);
lean_dec(v_unused_1055_);
v___x_1043_ = v_messageHead_1028_;
v_isShared_1044_ = v_isSharedCheck_1053_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v_messageHead_1028_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1053_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v_name_1025_);
lean_ctor_set(v___x_1045_, 1, v_value_1026_);
v___x_1046_ = lean_array_push(v___x_1041_, v___x_1045_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_uri_1040_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1046_);
lean_ctor_set_uint8(v_reuseFailAlloc_1052_, sizeof(void*)*2, v_method_1038_);
lean_ctor_set_uint8(v_reuseFailAlloc_1052_, sizeof(void*)*2 + 1, v_version_1039_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 2, v___x_1048_);
v___x_1050_ = v___x_1036_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_state_1029_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_input_1030_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_messageCount_1031_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_bodyBytesRead_1032_);
lean_ctor_set(v_reuseFailAlloc_1051_, 5, v_headerBytesRead_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1051_, sizeof(void*)*6, v_noMoreInput_1034_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v_messageHead_1057_; lean_object* v_state_1058_; lean_object* v_input_1059_; lean_object* v_messageCount_1060_; lean_object* v_bodyBytesRead_1061_; lean_object* v_headerBytesRead_1062_; uint8_t v_noMoreInput_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1084_; 
v_messageHead_1057_ = lean_ctor_get(v_reader_1027_, 2);
v_state_1058_ = lean_ctor_get(v_reader_1027_, 0);
v_input_1059_ = lean_ctor_get(v_reader_1027_, 1);
v_messageCount_1060_ = lean_ctor_get(v_reader_1027_, 3);
v_bodyBytesRead_1061_ = lean_ctor_get(v_reader_1027_, 4);
v_headerBytesRead_1062_ = lean_ctor_get(v_reader_1027_, 5);
v_noMoreInput_1063_ = lean_ctor_get_uint8(v_reader_1027_, sizeof(void*)*6);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_reader_1027_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1065_ = v_reader_1027_;
v_isShared_1066_ = v_isSharedCheck_1084_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_headerBytesRead_1062_);
lean_inc(v_bodyBytesRead_1061_);
lean_inc(v_messageCount_1060_);
lean_inc(v_messageHead_1057_);
lean_inc(v_input_1059_);
lean_inc(v_state_1058_);
lean_dec(v_reader_1027_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1084_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_status_1067_; uint8_t v_version_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1081_; 
v_status_1067_ = lean_ctor_get(v_messageHead_1057_, 0);
lean_inc(v_status_1067_);
v_version_1068_ = lean_ctor_get_uint8(v_messageHead_1057_, sizeof(void*)*2);
v___x_1069_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1024_, v_messageHead_1057_);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_messageHead_1057_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; lean_object* v_unused_1083_; 
v_unused_1082_ = lean_ctor_get(v_messageHead_1057_, 1);
lean_dec(v_unused_1082_);
v_unused_1083_ = lean_ctor_get(v_messageHead_1057_, 0);
lean_dec(v_unused_1083_);
v___x_1071_ = v_messageHead_1057_;
v_isShared_1072_ = v_isSharedCheck_1081_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_messageHead_1057_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1081_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_name_1025_);
lean_ctor_set(v___x_1073_, 1, v_value_1026_);
v___x_1074_ = lean_array_push(v___x_1069_, v___x_1073_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1074_);
v___x_1076_ = v___x_1071_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_status_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___x_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1080_, sizeof(void*)*2, v_version_1068_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 2, v___x_1076_);
v___x_1078_ = v___x_1065_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_state_1058_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_input_1059_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_messageCount_1060_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_bodyBytesRead_1061_);
lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_headerBytesRead_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*6, v_noMoreInput_1063_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1085_, lean_object* v_name_1086_, lean_object* v_value_1087_, lean_object* v_reader_1088_){
_start:
{
uint8_t v_dir_boxed_1089_; lean_object* v_res_1090_; 
v_dir_boxed_1089_ = lean_unbox(v_dir_1085_);
v_res_1090_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1089_, v_name_1086_, v_value_1087_, v_reader_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object* v_reader_1091_){
_start:
{
lean_object* v_input_1092_; lean_object* v_messageHead_1093_; lean_object* v_messageCount_1094_; lean_object* v_bodyBytesRead_1095_; lean_object* v_headerBytesRead_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1105_; 
v_input_1092_ = lean_ctor_get(v_reader_1091_, 1);
v_messageHead_1093_ = lean_ctor_get(v_reader_1091_, 2);
v_messageCount_1094_ = lean_ctor_get(v_reader_1091_, 3);
v_bodyBytesRead_1095_ = lean_ctor_get(v_reader_1091_, 4);
v_headerBytesRead_1096_ = lean_ctor_get(v_reader_1091_, 5);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_reader_1091_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v_reader_1091_, 0);
lean_dec(v_unused_1106_);
v___x_1098_ = v_reader_1091_;
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_headerBytesRead_1096_);
lean_inc(v_bodyBytesRead_1095_);
lean_inc(v_messageCount_1094_);
lean_inc(v_messageHead_1093_);
lean_inc(v_input_1092_);
lean_dec(v_reader_1091_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = lean_box(6);
v___x_1101_ = 1;
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1100_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_input_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_messageHead_1093_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_messageCount_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_bodyBytesRead_1095_);
lean_ctor_set(v_reuseFailAlloc_1104_, 5, v_headerBytesRead_1096_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*6, v___x_1101_);
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t v_dir_1107_, lean_object* v_reader_1108_){
_start:
{
lean_object* v_input_1109_; lean_object* v_messageHead_1110_; lean_object* v_messageCount_1111_; lean_object* v_bodyBytesRead_1112_; lean_object* v_headerBytesRead_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1122_; 
v_input_1109_ = lean_ctor_get(v_reader_1108_, 1);
v_messageHead_1110_ = lean_ctor_get(v_reader_1108_, 2);
v_messageCount_1111_ = lean_ctor_get(v_reader_1108_, 3);
v_bodyBytesRead_1112_ = lean_ctor_get(v_reader_1108_, 4);
v_headerBytesRead_1113_ = lean_ctor_get(v_reader_1108_, 5);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_reader_1108_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_reader_1108_, 0);
lean_dec(v_unused_1123_);
v___x_1115_ = v_reader_1108_;
v_isShared_1116_ = v_isSharedCheck_1122_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_headerBytesRead_1113_);
lean_inc(v_bodyBytesRead_1112_);
lean_inc(v_messageCount_1111_);
lean_inc(v_messageHead_1110_);
lean_inc(v_input_1109_);
lean_dec(v_reader_1108_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1122_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1120_; 
v___x_1117_ = lean_box(6);
v___x_1118_ = 1;
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1120_ = v___x_1115_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_input_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_messageHead_1110_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_messageCount_1111_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_bodyBytesRead_1112_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_headerBytesRead_1113_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*6, v___x_1118_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object* v_dir_1124_, lean_object* v_reader_1125_){
_start:
{
uint8_t v_dir_boxed_1126_; lean_object* v_res_1127_; 
v_dir_boxed_1126_ = lean_unbox(v_dir_1124_);
v_res_1127_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_1126_, v_reader_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1128_){
_start:
{
lean_object* v_input_1129_; lean_object* v_messageHead_1130_; lean_object* v_messageCount_1131_; lean_object* v_bodyBytesRead_1132_; lean_object* v_headerBytesRead_1133_; uint8_t v_noMoreInput_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1144_; 
v_input_1129_ = lean_ctor_get(v_reader_1128_, 1);
v_messageHead_1130_ = lean_ctor_get(v_reader_1128_, 2);
v_messageCount_1131_ = lean_ctor_get(v_reader_1128_, 3);
v_bodyBytesRead_1132_ = lean_ctor_get(v_reader_1128_, 4);
v_headerBytesRead_1133_ = lean_ctor_get(v_reader_1128_, 5);
v_noMoreInput_1134_ = lean_ctor_get_uint8(v_reader_1128_, sizeof(void*)*6);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_reader_1128_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_reader_1128_, 0);
lean_dec(v_unused_1145_);
v___x_1136_ = v_reader_1128_;
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_headerBytesRead_1133_);
lean_inc(v_bodyBytesRead_1132_);
lean_inc(v_messageCount_1131_);
lean_inc(v_messageHead_1130_);
lean_inc(v_input_1129_);
lean_dec(v_reader_1128_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1144_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1138_ = lean_box(5);
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v_messageCount_1131_, v___x_1139_);
lean_dec(v_messageCount_1131_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 3, v___x_1140_);
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1142_ = v___x_1136_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_input_1129_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_messageHead_1130_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_bodyBytesRead_1132_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_headerBytesRead_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1143_, sizeof(void*)*6, v_noMoreInput_1134_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1146_, lean_object* v_reader_1147_){
_start:
{
lean_object* v_input_1148_; lean_object* v_messageHead_1149_; lean_object* v_messageCount_1150_; lean_object* v_bodyBytesRead_1151_; lean_object* v_headerBytesRead_1152_; uint8_t v_noMoreInput_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1163_; 
v_input_1148_ = lean_ctor_get(v_reader_1147_, 1);
v_messageHead_1149_ = lean_ctor_get(v_reader_1147_, 2);
v_messageCount_1150_ = lean_ctor_get(v_reader_1147_, 3);
v_bodyBytesRead_1151_ = lean_ctor_get(v_reader_1147_, 4);
v_headerBytesRead_1152_ = lean_ctor_get(v_reader_1147_, 5);
v_noMoreInput_1153_ = lean_ctor_get_uint8(v_reader_1147_, sizeof(void*)*6);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_reader_1147_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_reader_1147_, 0);
lean_dec(v_unused_1164_);
v___x_1155_ = v_reader_1147_;
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_headerBytesRead_1152_);
lean_inc(v_bodyBytesRead_1151_);
lean_inc(v_messageCount_1150_);
lean_inc(v_messageHead_1149_);
lean_inc(v_input_1148_);
lean_dec(v_reader_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1163_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1157_ = lean_box(5);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_messageCount_1150_, v___x_1158_);
lean_dec(v_messageCount_1150_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 3, v___x_1159_);
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1161_ = v___x_1155_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_input_1148_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_messageHead_1149_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_bodyBytesRead_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_headerBytesRead_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, sizeof(void*)*6, v_noMoreInput_1153_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object* v_dir_1165_, lean_object* v_reader_1166_){
_start:
{
uint8_t v_dir_boxed_1167_; lean_object* v_res_1168_; 
v_dir_boxed_1167_ = lean_unbox(v_dir_1165_);
v_res_1168_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_1167_, v_reader_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object* v_error_1169_, lean_object* v_reader_1170_){
_start:
{
lean_object* v_input_1171_; lean_object* v_messageHead_1172_; lean_object* v_messageCount_1173_; lean_object* v_bodyBytesRead_1174_; lean_object* v_headerBytesRead_1175_; uint8_t v_noMoreInput_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1184_; 
v_input_1171_ = lean_ctor_get(v_reader_1170_, 1);
v_messageHead_1172_ = lean_ctor_get(v_reader_1170_, 2);
v_messageCount_1173_ = lean_ctor_get(v_reader_1170_, 3);
v_bodyBytesRead_1174_ = lean_ctor_get(v_reader_1170_, 4);
v_headerBytesRead_1175_ = lean_ctor_get(v_reader_1170_, 5);
v_noMoreInput_1176_ = lean_ctor_get_uint8(v_reader_1170_, sizeof(void*)*6);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_reader_1170_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v_reader_1170_, 0);
lean_dec(v_unused_1185_);
v___x_1178_ = v_reader_1170_;
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_headerBytesRead_1175_);
lean_inc(v_bodyBytesRead_1174_);
lean_inc(v_messageCount_1173_);
lean_inc(v_messageHead_1172_);
lean_inc(v_input_1171_);
lean_dec(v_reader_1170_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_error_1169_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_input_1171_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_messageHead_1172_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_messageCount_1173_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_bodyBytesRead_1174_);
lean_ctor_set(v_reuseFailAlloc_1183_, 5, v_headerBytesRead_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1183_, sizeof(void*)*6, v_noMoreInput_1176_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t v_dir_1186_, lean_object* v_error_1187_, lean_object* v_reader_1188_){
_start:
{
lean_object* v_input_1189_; lean_object* v_messageHead_1190_; lean_object* v_messageCount_1191_; lean_object* v_bodyBytesRead_1192_; lean_object* v_headerBytesRead_1193_; uint8_t v_noMoreInput_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1202_; 
v_input_1189_ = lean_ctor_get(v_reader_1188_, 1);
v_messageHead_1190_ = lean_ctor_get(v_reader_1188_, 2);
v_messageCount_1191_ = lean_ctor_get(v_reader_1188_, 3);
v_bodyBytesRead_1192_ = lean_ctor_get(v_reader_1188_, 4);
v_headerBytesRead_1193_ = lean_ctor_get(v_reader_1188_, 5);
v_noMoreInput_1194_ = lean_ctor_get_uint8(v_reader_1188_, sizeof(void*)*6);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_reader_1188_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; 
v_unused_1203_ = lean_ctor_get(v_reader_1188_, 0);
lean_dec(v_unused_1203_);
v___x_1196_ = v_reader_1188_;
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_headerBytesRead_1193_);
lean_inc(v_bodyBytesRead_1192_);
lean_inc(v_messageCount_1191_);
lean_inc(v_messageHead_1190_);
lean_inc(v_input_1189_);
lean_dec(v_reader_1188_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1198_, 0, v_error_1187_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_input_1189_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_messageHead_1190_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_messageCount_1191_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_bodyBytesRead_1192_);
lean_ctor_set(v_reuseFailAlloc_1201_, 5, v_headerBytesRead_1193_);
lean_ctor_set_uint8(v_reuseFailAlloc_1201_, sizeof(void*)*6, v_noMoreInput_1194_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object* v_dir_1204_, lean_object* v_error_1205_, lean_object* v_reader_1206_){
_start:
{
uint8_t v_dir_boxed_1207_; lean_object* v_res_1208_; 
v_dir_boxed_1207_ = lean_unbox(v_dir_1204_);
v_res_1208_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_1207_, v_error_1205_, v_reader_1206_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1209_, lean_object* v_reader_1210_){
_start:
{
lean_object* v_input_1211_; lean_object* v_messageCount_1212_; uint8_t v_noMoreInput_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1223_; 
v_input_1211_ = lean_ctor_get(v_reader_1210_, 1);
v_messageCount_1212_ = lean_ctor_get(v_reader_1210_, 3);
v_noMoreInput_1213_ = lean_ctor_get_uint8(v_reader_1210_, sizeof(void*)*6);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_reader_1210_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; lean_object* v_unused_1225_; lean_object* v_unused_1226_; lean_object* v_unused_1227_; 
v_unused_1224_ = lean_ctor_get(v_reader_1210_, 5);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_reader_1210_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_reader_1210_, 2);
lean_dec(v_unused_1226_);
v_unused_1227_ = lean_ctor_get(v_reader_1210_, 0);
lean_dec(v_unused_1227_);
v___x_1215_ = v_reader_1210_;
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_messageCount_1212_);
lean_inc(v_input_1211_);
lean_dec(v_reader_1210_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1223_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1209_);
v___x_1219_ = lean_unsigned_to_nat(0u);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 5, v___x_1219_);
lean_ctor_set(v___x_1215_, 4, v___x_1219_);
lean_ctor_set(v___x_1215_, 2, v___x_1218_);
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1221_ = v___x_1215_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_input_1211_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_messageCount_1212_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1222_, 5, v___x_1219_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*6, v_noMoreInput_1213_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1228_, lean_object* v_reader_1229_){
_start:
{
uint8_t v_dir_boxed_1230_; lean_object* v_res_1231_; 
v_dir_boxed_1230_ = lean_unbox(v_dir_1228_);
v_res_1231_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1230_, v_reader_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1232_){
_start:
{
lean_object* v_input_1233_; lean_object* v_state_1234_; uint8_t v_noMoreInput_1235_; lean_object* v_array_1236_; lean_object* v_idx_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_input_1233_ = lean_ctor_get(v_reader_1232_, 1);
v_state_1234_ = lean_ctor_get(v_reader_1232_, 0);
v_noMoreInput_1235_ = lean_ctor_get_uint8(v_reader_1232_, sizeof(void*)*6);
v_array_1236_ = lean_ctor_get(v_input_1233_, 0);
v_idx_1237_ = lean_ctor_get(v_input_1233_, 1);
v___x_1238_ = lean_byte_array_size(v_array_1236_);
v___x_1239_ = lean_nat_dec_le(v___x_1238_, v_idx_1237_);
if (v___x_1239_ == 0)
{
return v___x_1239_;
}
else
{
if (v_noMoreInput_1235_ == 0)
{
switch(lean_obj_tag(v_state_1234_))
{
case 5:
{
return v_noMoreInput_1235_;
}
case 6:
{
return v_noMoreInput_1235_;
}
case 7:
{
return v_noMoreInput_1235_;
}
case 3:
{
return v_noMoreInput_1235_;
}
default: 
{
return v___x_1239_;
}
}
}
else
{
uint8_t v___x_1240_; 
v___x_1240_ = 0;
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1241_);
lean_dec_ref(v_reader_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1244_, lean_object* v_reader_1245_){
_start:
{
lean_object* v_input_1246_; lean_object* v_state_1247_; uint8_t v_noMoreInput_1248_; lean_object* v_array_1249_; lean_object* v_idx_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_input_1246_ = lean_ctor_get(v_reader_1245_, 1);
v_state_1247_ = lean_ctor_get(v_reader_1245_, 0);
v_noMoreInput_1248_ = lean_ctor_get_uint8(v_reader_1245_, sizeof(void*)*6);
v_array_1249_ = lean_ctor_get(v_input_1246_, 0);
v_idx_1250_ = lean_ctor_get(v_input_1246_, 1);
v___x_1251_ = lean_byte_array_size(v_array_1249_);
v___x_1252_ = lean_nat_dec_le(v___x_1251_, v_idx_1250_);
if (v___x_1252_ == 0)
{
return v___x_1252_;
}
else
{
if (v_noMoreInput_1248_ == 0)
{
switch(lean_obj_tag(v_state_1247_))
{
case 5:
{
return v_noMoreInput_1248_;
}
case 6:
{
return v_noMoreInput_1248_;
}
case 7:
{
return v_noMoreInput_1248_;
}
case 3:
{
return v_noMoreInput_1248_;
}
default: 
{
return v___x_1252_;
}
}
}
else
{
uint8_t v___x_1253_; 
v___x_1253_ = 0;
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1254_, lean_object* v_reader_1255_){
_start:
{
uint8_t v_dir_boxed_1256_; uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_dir_boxed_1256_ = lean_unbox(v_dir_1254_);
v_res_1257_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1256_, v_reader_1255_);
lean_dec_ref(v_reader_1255_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object* v_reader_1259_){
_start:
{
lean_object* v_state_1260_; 
v_state_1260_ = lean_ctor_get(v_reader_1259_, 0);
lean_inc(v_state_1260_);
lean_dec_ref(v_reader_1259_);
if (lean_obj_tag(v_state_1260_) == 7)
{
lean_object* v_error_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_error_1261_ = lean_ctor_get(v_state_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_state_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v_state_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_error_1261_);
lean_dec(v_state_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_error_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_state_1260_);
v___x_1269_ = lean_box(0);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t v_dir_1270_, lean_object* v_reader_1271_){
_start:
{
lean_object* v_state_1272_; 
v_state_1272_ = lean_ctor_get(v_reader_1271_, 0);
lean_inc(v_state_1272_);
lean_dec_ref(v_reader_1271_);
if (lean_obj_tag(v_state_1272_) == 7)
{
lean_object* v_error_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_error_1273_ = lean_ctor_get(v_state_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_state_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v_state_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_error_1273_);
lean_dec(v_state_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 1);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_error_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_state_1272_);
v___x_1281_ = lean_box(0);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object* v_dir_1282_, lean_object* v_reader_1283_){
_start:
{
uint8_t v_dir_boxed_1284_; lean_object* v_res_1285_; 
v_dir_boxed_1284_ = lean_unbox(v_dir_1282_);
v_res_1285_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_1284_, v_reader_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1286_){
_start:
{
lean_object* v_input_1287_; lean_object* v_array_1288_; lean_object* v_idx_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_input_1287_ = lean_ctor_get(v_reader_1286_, 1);
v_array_1288_ = lean_ctor_get(v_input_1287_, 0);
v_idx_1289_ = lean_ctor_get(v_input_1287_, 1);
v___x_1290_ = lean_byte_array_size(v_array_1288_);
v___x_1291_ = lean_nat_sub(v___x_1290_, v_idx_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1292_);
lean_dec_ref(v_reader_1292_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1294_, lean_object* v_reader_1295_){
_start:
{
lean_object* v_input_1296_; lean_object* v_array_1297_; lean_object* v_idx_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_input_1296_ = lean_ctor_get(v_reader_1295_, 1);
v_array_1297_ = lean_ctor_get(v_input_1296_, 0);
v_idx_1298_ = lean_ctor_get(v_input_1296_, 1);
v___x_1299_ = lean_byte_array_size(v_array_1297_);
v___x_1300_ = lean_nat_sub(v___x_1299_, v_idx_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1301_, lean_object* v_reader_1302_){
_start:
{
uint8_t v_dir_boxed_1303_; lean_object* v_res_1304_; 
v_dir_boxed_1303_ = lean_unbox(v_dir_1301_);
v_res_1304_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1303_, v_reader_1302_);
lean_dec_ref(v_reader_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1305_, lean_object* v_reader_1306_){
_start:
{
lean_object* v_input_1307_; lean_object* v_state_1308_; lean_object* v_messageHead_1309_; lean_object* v_messageCount_1310_; lean_object* v_bodyBytesRead_1311_; lean_object* v_headerBytesRead_1312_; uint8_t v_noMoreInput_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1330_; 
v_input_1307_ = lean_ctor_get(v_reader_1306_, 1);
v_state_1308_ = lean_ctor_get(v_reader_1306_, 0);
v_messageHead_1309_ = lean_ctor_get(v_reader_1306_, 2);
v_messageCount_1310_ = lean_ctor_get(v_reader_1306_, 3);
v_bodyBytesRead_1311_ = lean_ctor_get(v_reader_1306_, 4);
v_headerBytesRead_1312_ = lean_ctor_get(v_reader_1306_, 5);
v_noMoreInput_1313_ = lean_ctor_get_uint8(v_reader_1306_, sizeof(void*)*6);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_reader_1306_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1315_ = v_reader_1306_;
v_isShared_1316_ = v_isSharedCheck_1330_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_headerBytesRead_1312_);
lean_inc(v_bodyBytesRead_1311_);
lean_inc(v_messageCount_1310_);
lean_inc(v_messageHead_1309_);
lean_inc(v_input_1307_);
lean_inc(v_state_1308_);
lean_dec(v_reader_1306_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1330_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v_array_1317_; lean_object* v_idx_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1329_; 
v_array_1317_ = lean_ctor_get(v_input_1307_, 0);
v_idx_1318_ = lean_ctor_get(v_input_1307_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_input_1307_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1320_ = v_input_1307_;
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_idx_1318_);
lean_inc(v_array_1317_);
lean_dec(v_input_1307_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_nat_add(v_idx_1318_, v_n_1305_);
lean_dec(v_idx_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_array_1317_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v___x_1324_);
v___x_1326_ = v___x_1315_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_state_1308_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_messageHead_1309_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_messageCount_1310_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_bodyBytesRead_1311_);
lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_headerBytesRead_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*6, v_noMoreInput_1313_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1331_, lean_object* v_reader_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1331_, v_reader_1332_);
lean_dec(v_n_1331_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1334_, lean_object* v_n_1335_, lean_object* v_reader_1336_){
_start:
{
lean_object* v_input_1337_; lean_object* v_state_1338_; lean_object* v_messageHead_1339_; lean_object* v_messageCount_1340_; lean_object* v_bodyBytesRead_1341_; lean_object* v_headerBytesRead_1342_; uint8_t v_noMoreInput_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1360_; 
v_input_1337_ = lean_ctor_get(v_reader_1336_, 1);
v_state_1338_ = lean_ctor_get(v_reader_1336_, 0);
v_messageHead_1339_ = lean_ctor_get(v_reader_1336_, 2);
v_messageCount_1340_ = lean_ctor_get(v_reader_1336_, 3);
v_bodyBytesRead_1341_ = lean_ctor_get(v_reader_1336_, 4);
v_headerBytesRead_1342_ = lean_ctor_get(v_reader_1336_, 5);
v_noMoreInput_1343_ = lean_ctor_get_uint8(v_reader_1336_, sizeof(void*)*6);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_reader_1336_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1345_ = v_reader_1336_;
v_isShared_1346_ = v_isSharedCheck_1360_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_headerBytesRead_1342_);
lean_inc(v_bodyBytesRead_1341_);
lean_inc(v_messageCount_1340_);
lean_inc(v_messageHead_1339_);
lean_inc(v_input_1337_);
lean_inc(v_state_1338_);
lean_dec(v_reader_1336_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1360_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_array_1347_; lean_object* v_idx_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_array_1347_ = lean_ctor_get(v_input_1337_, 0);
v_idx_1348_ = lean_ctor_get(v_input_1337_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_input_1337_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1350_ = v_input_1337_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_idx_1348_);
lean_inc(v_array_1347_);
lean_dec(v_input_1337_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_nat_add(v_idx_1348_, v_n_1335_);
lean_dec(v_idx_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_array_1347_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v___x_1354_);
v___x_1356_ = v___x_1345_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_state_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_messageHead_1339_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_messageCount_1340_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_bodyBytesRead_1341_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_headerBytesRead_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1357_, sizeof(void*)*6, v_noMoreInput_1343_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1361_, lean_object* v_n_1362_, lean_object* v_reader_1363_){
_start:
{
uint8_t v_dir_boxed_1364_; lean_object* v_res_1365_; 
v_dir_boxed_1364_ = lean_unbox(v_dir_1361_);
v_res_1365_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1364_, v_n_1362_, v_reader_1363_);
lean_dec(v_n_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1368_){
_start:
{
lean_object* v_input_1369_; lean_object* v_messageHead_1370_; lean_object* v_messageCount_1371_; uint8_t v_noMoreInput_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1381_; 
v_input_1369_ = lean_ctor_get(v_reader_1368_, 1);
v_messageHead_1370_ = lean_ctor_get(v_reader_1368_, 2);
v_messageCount_1371_ = lean_ctor_get(v_reader_1368_, 3);
v_noMoreInput_1372_ = lean_ctor_get_uint8(v_reader_1368_, sizeof(void*)*6);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_reader_1368_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; lean_object* v_unused_1383_; lean_object* v_unused_1384_; 
v_unused_1382_ = lean_ctor_get(v_reader_1368_, 5);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_reader_1368_, 4);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_reader_1368_, 0);
lean_dec(v_unused_1384_);
v___x_1374_ = v_reader_1368_;
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_messageCount_1371_);
lean_inc(v_messageHead_1370_);
lean_inc(v_input_1369_);
lean_dec(v_reader_1368_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1381_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 5, v___x_1376_);
lean_ctor_set(v___x_1374_, 4, v___x_1376_);
lean_ctor_set(v___x_1374_, 0, v___x_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_input_1369_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_messageHead_1370_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_messageCount_1371_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1380_, 5, v___x_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*6, v_noMoreInput_1372_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1385_, lean_object* v_reader_1386_){
_start:
{
lean_object* v_input_1387_; lean_object* v_messageHead_1388_; lean_object* v_messageCount_1389_; uint8_t v_noMoreInput_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1399_; 
v_input_1387_ = lean_ctor_get(v_reader_1386_, 1);
v_messageHead_1388_ = lean_ctor_get(v_reader_1386_, 2);
v_messageCount_1389_ = lean_ctor_get(v_reader_1386_, 3);
v_noMoreInput_1390_ = lean_ctor_get_uint8(v_reader_1386_, sizeof(void*)*6);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_reader_1386_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; lean_object* v_unused_1401_; lean_object* v_unused_1402_; 
v_unused_1400_ = lean_ctor_get(v_reader_1386_, 5);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_reader_1386_, 4);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_reader_1386_, 0);
lean_dec(v_unused_1402_);
v___x_1392_ = v_reader_1386_;
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_messageCount_1389_);
lean_inc(v_messageHead_1388_);
lean_inc(v_input_1387_);
lean_dec(v_reader_1386_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v___x_1395_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 5, v___x_1394_);
lean_ctor_set(v___x_1392_, 4, v___x_1394_);
lean_ctor_set(v___x_1392_, 0, v___x_1395_);
v___x_1397_ = v___x_1392_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_input_1387_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_messageHead_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_messageCount_1389_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1398_, 5, v___x_1394_);
lean_ctor_set_uint8(v_reuseFailAlloc_1398_, sizeof(void*)*6, v_noMoreInput_1390_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1403_, lean_object* v_reader_1404_){
_start:
{
uint8_t v_dir_boxed_1405_; lean_object* v_res_1406_; 
v_dir_boxed_1405_ = lean_unbox(v_dir_1403_);
v_res_1406_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1405_, v_reader_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1407_, lean_object* v_reader_1408_){
_start:
{
lean_object* v_state_1409_; lean_object* v_input_1410_; lean_object* v_messageHead_1411_; lean_object* v_messageCount_1412_; lean_object* v_bodyBytesRead_1413_; lean_object* v_headerBytesRead_1414_; uint8_t v_noMoreInput_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1423_; 
v_state_1409_ = lean_ctor_get(v_reader_1408_, 0);
v_input_1410_ = lean_ctor_get(v_reader_1408_, 1);
v_messageHead_1411_ = lean_ctor_get(v_reader_1408_, 2);
v_messageCount_1412_ = lean_ctor_get(v_reader_1408_, 3);
v_bodyBytesRead_1413_ = lean_ctor_get(v_reader_1408_, 4);
v_headerBytesRead_1414_ = lean_ctor_get(v_reader_1408_, 5);
v_noMoreInput_1415_ = lean_ctor_get_uint8(v_reader_1408_, sizeof(void*)*6);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_reader_1408_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1417_ = v_reader_1408_;
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_headerBytesRead_1414_);
lean_inc(v_bodyBytesRead_1413_);
lean_inc(v_messageCount_1412_);
lean_inc(v_messageHead_1411_);
lean_inc(v_input_1410_);
lean_inc(v_state_1409_);
lean_dec(v_reader_1408_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1423_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_nat_add(v_bodyBytesRead_1413_, v_n_1407_);
lean_dec(v_bodyBytesRead_1413_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 4, v___x_1419_);
v___x_1421_ = v___x_1417_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_state_1409_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_input_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_messageHead_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_messageCount_1412_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1422_, 5, v_headerBytesRead_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1422_, sizeof(void*)*6, v_noMoreInput_1415_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1424_, lean_object* v_reader_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1424_, v_reader_1425_);
lean_dec(v_n_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1427_, lean_object* v_n_1428_, lean_object* v_reader_1429_){
_start:
{
lean_object* v_state_1430_; lean_object* v_input_1431_; lean_object* v_messageHead_1432_; lean_object* v_messageCount_1433_; lean_object* v_bodyBytesRead_1434_; lean_object* v_headerBytesRead_1435_; uint8_t v_noMoreInput_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_state_1430_ = lean_ctor_get(v_reader_1429_, 0);
v_input_1431_ = lean_ctor_get(v_reader_1429_, 1);
v_messageHead_1432_ = lean_ctor_get(v_reader_1429_, 2);
v_messageCount_1433_ = lean_ctor_get(v_reader_1429_, 3);
v_bodyBytesRead_1434_ = lean_ctor_get(v_reader_1429_, 4);
v_headerBytesRead_1435_ = lean_ctor_get(v_reader_1429_, 5);
v_noMoreInput_1436_ = lean_ctor_get_uint8(v_reader_1429_, sizeof(void*)*6);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_reader_1429_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v_reader_1429_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_headerBytesRead_1435_);
lean_inc(v_bodyBytesRead_1434_);
lean_inc(v_messageCount_1433_);
lean_inc(v_messageHead_1432_);
lean_inc(v_input_1431_);
lean_inc(v_state_1430_);
lean_dec(v_reader_1429_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_nat_add(v_bodyBytesRead_1434_, v_n_1428_);
lean_dec(v_bodyBytesRead_1434_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 4, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_state_1430_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_input_1431_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_messageHead_1432_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_messageCount_1433_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 5, v_headerBytesRead_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1443_, sizeof(void*)*6, v_noMoreInput_1436_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1445_, lean_object* v_n_1446_, lean_object* v_reader_1447_){
_start:
{
uint8_t v_dir_boxed_1448_; lean_object* v_res_1449_; 
v_dir_boxed_1448_ = lean_unbox(v_dir_1445_);
v_res_1449_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1448_, v_n_1446_, v_reader_1447_);
lean_dec(v_n_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1450_, lean_object* v_reader_1451_){
_start:
{
lean_object* v_state_1452_; lean_object* v_input_1453_; lean_object* v_messageHead_1454_; lean_object* v_messageCount_1455_; lean_object* v_bodyBytesRead_1456_; lean_object* v_headerBytesRead_1457_; uint8_t v_noMoreInput_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_state_1452_ = lean_ctor_get(v_reader_1451_, 0);
v_input_1453_ = lean_ctor_get(v_reader_1451_, 1);
v_messageHead_1454_ = lean_ctor_get(v_reader_1451_, 2);
v_messageCount_1455_ = lean_ctor_get(v_reader_1451_, 3);
v_bodyBytesRead_1456_ = lean_ctor_get(v_reader_1451_, 4);
v_headerBytesRead_1457_ = lean_ctor_get(v_reader_1451_, 5);
v_noMoreInput_1458_ = lean_ctor_get_uint8(v_reader_1451_, sizeof(void*)*6);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_reader_1451_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1460_ = v_reader_1451_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_headerBytesRead_1457_);
lean_inc(v_bodyBytesRead_1456_);
lean_inc(v_messageCount_1455_);
lean_inc(v_messageHead_1454_);
lean_inc(v_input_1453_);
lean_inc(v_state_1452_);
lean_dec(v_reader_1451_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_nat_add(v_headerBytesRead_1457_, v_n_1450_);
lean_dec(v_headerBytesRead_1457_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 5, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_state_1452_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_input_1453_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_messageHead_1454_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_messageCount_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_bodyBytesRead_1456_);
lean_ctor_set(v_reuseFailAlloc_1465_, 5, v___x_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*6, v_noMoreInput_1458_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1467_, lean_object* v_reader_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1467_, v_reader_1468_);
lean_dec(v_n_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1470_, lean_object* v_n_1471_, lean_object* v_reader_1472_){
_start:
{
lean_object* v_state_1473_; lean_object* v_input_1474_; lean_object* v_messageHead_1475_; lean_object* v_messageCount_1476_; lean_object* v_bodyBytesRead_1477_; lean_object* v_headerBytesRead_1478_; uint8_t v_noMoreInput_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1487_; 
v_state_1473_ = lean_ctor_get(v_reader_1472_, 0);
v_input_1474_ = lean_ctor_get(v_reader_1472_, 1);
v_messageHead_1475_ = lean_ctor_get(v_reader_1472_, 2);
v_messageCount_1476_ = lean_ctor_get(v_reader_1472_, 3);
v_bodyBytesRead_1477_ = lean_ctor_get(v_reader_1472_, 4);
v_headerBytesRead_1478_ = lean_ctor_get(v_reader_1472_, 5);
v_noMoreInput_1479_ = lean_ctor_get_uint8(v_reader_1472_, sizeof(void*)*6);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_reader_1472_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1481_ = v_reader_1472_;
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_headerBytesRead_1478_);
lean_inc(v_bodyBytesRead_1477_);
lean_inc(v_messageCount_1476_);
lean_inc(v_messageHead_1475_);
lean_inc(v_input_1474_);
lean_inc(v_state_1473_);
lean_dec(v_reader_1472_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1487_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_nat_add(v_headerBytesRead_1478_, v_n_1471_);
lean_dec(v_headerBytesRead_1478_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 5, v___x_1483_);
v___x_1485_ = v___x_1481_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_state_1473_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_input_1474_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_messageHead_1475_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_messageCount_1476_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_bodyBytesRead_1477_);
lean_ctor_set(v_reuseFailAlloc_1486_, 5, v___x_1483_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*6, v_noMoreInput_1479_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1488_, lean_object* v_n_1489_, lean_object* v_reader_1490_){
_start:
{
uint8_t v_dir_boxed_1491_; lean_object* v_res_1492_; 
v_dir_boxed_1491_ = lean_unbox(v_dir_1488_);
v_res_1492_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1491_, v_n_1489_, v_reader_1490_);
lean_dec(v_n_1489_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1493_, lean_object* v_reader_1494_){
_start:
{
lean_object* v_input_1495_; lean_object* v_messageHead_1496_; lean_object* v_messageCount_1497_; lean_object* v_bodyBytesRead_1498_; lean_object* v_headerBytesRead_1499_; uint8_t v_noMoreInput_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1509_; 
v_input_1495_ = lean_ctor_get(v_reader_1494_, 1);
v_messageHead_1496_ = lean_ctor_get(v_reader_1494_, 2);
v_messageCount_1497_ = lean_ctor_get(v_reader_1494_, 3);
v_bodyBytesRead_1498_ = lean_ctor_get(v_reader_1494_, 4);
v_headerBytesRead_1499_ = lean_ctor_get(v_reader_1494_, 5);
v_noMoreInput_1500_ = lean_ctor_get_uint8(v_reader_1494_, sizeof(void*)*6);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_reader_1494_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_reader_1494_, 0);
lean_dec(v_unused_1510_);
v___x_1502_ = v_reader_1494_;
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_headerBytesRead_1499_);
lean_inc(v_bodyBytesRead_1498_);
lean_inc(v_messageCount_1497_);
lean_inc(v_messageHead_1496_);
lean_inc(v_input_1495_);
lean_dec(v_reader_1494_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1509_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v_size_1493_);
v___x_1505_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 0, v___x_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_input_1495_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_messageHead_1496_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_messageCount_1497_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_bodyBytesRead_1498_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_headerBytesRead_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*6, v_noMoreInput_1500_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1511_, lean_object* v_size_1512_, lean_object* v_reader_1513_){
_start:
{
lean_object* v_input_1514_; lean_object* v_messageHead_1515_; lean_object* v_messageCount_1516_; lean_object* v_bodyBytesRead_1517_; lean_object* v_headerBytesRead_1518_; uint8_t v_noMoreInput_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1528_; 
v_input_1514_ = lean_ctor_get(v_reader_1513_, 1);
v_messageHead_1515_ = lean_ctor_get(v_reader_1513_, 2);
v_messageCount_1516_ = lean_ctor_get(v_reader_1513_, 3);
v_bodyBytesRead_1517_ = lean_ctor_get(v_reader_1513_, 4);
v_headerBytesRead_1518_ = lean_ctor_get(v_reader_1513_, 5);
v_noMoreInput_1519_ = lean_ctor_get_uint8(v_reader_1513_, sizeof(void*)*6);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_reader_1513_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_reader_1513_, 0);
lean_dec(v_unused_1529_);
v___x_1521_ = v_reader_1513_;
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_headerBytesRead_1518_);
lean_inc(v_bodyBytesRead_1517_);
lean_inc(v_messageCount_1516_);
lean_inc(v_messageHead_1515_);
lean_inc(v_input_1514_);
lean_dec(v_reader_1513_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1528_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v_size_1512_);
v___x_1524_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1524_);
v___x_1526_ = v___x_1521_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_input_1514_);
lean_ctor_set(v_reuseFailAlloc_1527_, 2, v_messageHead_1515_);
lean_ctor_set(v_reuseFailAlloc_1527_, 3, v_messageCount_1516_);
lean_ctor_set(v_reuseFailAlloc_1527_, 4, v_bodyBytesRead_1517_);
lean_ctor_set(v_reuseFailAlloc_1527_, 5, v_headerBytesRead_1518_);
lean_ctor_set_uint8(v_reuseFailAlloc_1527_, sizeof(void*)*6, v_noMoreInput_1519_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1530_, lean_object* v_size_1531_, lean_object* v_reader_1532_){
_start:
{
uint8_t v_dir_boxed_1533_; lean_object* v_res_1534_; 
v_dir_boxed_1533_ = lean_unbox(v_dir_1530_);
v_res_1534_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1533_, v_size_1531_, v_reader_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1537_){
_start:
{
lean_object* v_input_1538_; lean_object* v_messageHead_1539_; lean_object* v_messageCount_1540_; lean_object* v_bodyBytesRead_1541_; lean_object* v_headerBytesRead_1542_; uint8_t v_noMoreInput_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1551_; 
v_input_1538_ = lean_ctor_get(v_reader_1537_, 1);
v_messageHead_1539_ = lean_ctor_get(v_reader_1537_, 2);
v_messageCount_1540_ = lean_ctor_get(v_reader_1537_, 3);
v_bodyBytesRead_1541_ = lean_ctor_get(v_reader_1537_, 4);
v_headerBytesRead_1542_ = lean_ctor_get(v_reader_1537_, 5);
v_noMoreInput_1543_ = lean_ctor_get_uint8(v_reader_1537_, sizeof(void*)*6);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_reader_1537_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_reader_1537_, 0);
lean_dec(v_unused_1552_);
v___x_1545_ = v_reader_1537_;
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_headerBytesRead_1542_);
lean_inc(v_bodyBytesRead_1541_);
lean_inc(v_messageCount_1540_);
lean_inc(v_messageHead_1539_);
lean_inc(v_input_1538_);
lean_dec(v_reader_1537_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1551_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1547_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1547_);
v___x_1549_ = v___x_1545_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_input_1538_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_messageHead_1539_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_messageCount_1540_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_bodyBytesRead_1541_);
lean_ctor_set(v_reuseFailAlloc_1550_, 5, v_headerBytesRead_1542_);
lean_ctor_set_uint8(v_reuseFailAlloc_1550_, sizeof(void*)*6, v_noMoreInput_1543_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1553_, lean_object* v_reader_1554_){
_start:
{
lean_object* v_input_1555_; lean_object* v_messageHead_1556_; lean_object* v_messageCount_1557_; lean_object* v_bodyBytesRead_1558_; lean_object* v_headerBytesRead_1559_; uint8_t v_noMoreInput_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1568_; 
v_input_1555_ = lean_ctor_get(v_reader_1554_, 1);
v_messageHead_1556_ = lean_ctor_get(v_reader_1554_, 2);
v_messageCount_1557_ = lean_ctor_get(v_reader_1554_, 3);
v_bodyBytesRead_1558_ = lean_ctor_get(v_reader_1554_, 4);
v_headerBytesRead_1559_ = lean_ctor_get(v_reader_1554_, 5);
v_noMoreInput_1560_ = lean_ctor_get_uint8(v_reader_1554_, sizeof(void*)*6);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_reader_1554_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_reader_1554_, 0);
lean_dec(v_unused_1569_);
v___x_1562_ = v_reader_1554_;
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_headerBytesRead_1559_);
lean_inc(v_bodyBytesRead_1558_);
lean_inc(v_messageCount_1557_);
lean_inc(v_messageHead_1556_);
lean_inc(v_input_1555_);
lean_dec(v_reader_1554_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1568_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_input_1555_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_messageHead_1556_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_messageCount_1557_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_bodyBytesRead_1558_);
lean_ctor_set(v_reuseFailAlloc_1567_, 5, v_headerBytesRead_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1567_, sizeof(void*)*6, v_noMoreInput_1560_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1570_, lean_object* v_reader_1571_){
_start:
{
uint8_t v_dir_boxed_1572_; lean_object* v_res_1573_; 
v_dir_boxed_1572_ = lean_unbox(v_dir_1570_);
v_res_1573_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1572_, v_reader_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object* v_reader_1574_){
_start:
{
lean_object* v_state_1575_; lean_object* v_input_1576_; lean_object* v_messageHead_1577_; lean_object* v_messageCount_1578_; lean_object* v_bodyBytesRead_1579_; lean_object* v_headerBytesRead_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1588_; 
v_state_1575_ = lean_ctor_get(v_reader_1574_, 0);
v_input_1576_ = lean_ctor_get(v_reader_1574_, 1);
v_messageHead_1577_ = lean_ctor_get(v_reader_1574_, 2);
v_messageCount_1578_ = lean_ctor_get(v_reader_1574_, 3);
v_bodyBytesRead_1579_ = lean_ctor_get(v_reader_1574_, 4);
v_headerBytesRead_1580_ = lean_ctor_get(v_reader_1574_, 5);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_reader_1574_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1582_ = v_reader_1574_;
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_headerBytesRead_1580_);
lean_inc(v_bodyBytesRead_1579_);
lean_inc(v_messageCount_1578_);
lean_inc(v_messageHead_1577_);
lean_inc(v_input_1576_);
lean_inc(v_state_1575_);
lean_dec(v_reader_1574_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v___x_1584_; lean_object* v___x_1586_; 
v___x_1584_ = 1;
if (v_isShared_1583_ == 0)
{
v___x_1586_ = v___x_1582_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_state_1575_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_input_1576_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_messageHead_1577_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_messageCount_1578_);
lean_ctor_set(v_reuseFailAlloc_1587_, 4, v_bodyBytesRead_1579_);
lean_ctor_set(v_reuseFailAlloc_1587_, 5, v_headerBytesRead_1580_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_ctor_set_uint8(v___x_1586_, sizeof(void*)*6, v___x_1584_);
return v___x_1586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t v_dir_1589_, lean_object* v_reader_1590_){
_start:
{
lean_object* v_state_1591_; lean_object* v_input_1592_; lean_object* v_messageHead_1593_; lean_object* v_messageCount_1594_; lean_object* v_bodyBytesRead_1595_; lean_object* v_headerBytesRead_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
v_state_1591_ = lean_ctor_get(v_reader_1590_, 0);
v_input_1592_ = lean_ctor_get(v_reader_1590_, 1);
v_messageHead_1593_ = lean_ctor_get(v_reader_1590_, 2);
v_messageCount_1594_ = lean_ctor_get(v_reader_1590_, 3);
v_bodyBytesRead_1595_ = lean_ctor_get(v_reader_1590_, 4);
v_headerBytesRead_1596_ = lean_ctor_get(v_reader_1590_, 5);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_reader_1590_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v_reader_1590_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_headerBytesRead_1596_);
lean_inc(v_bodyBytesRead_1595_);
lean_inc(v_messageCount_1594_);
lean_inc(v_messageHead_1593_);
lean_inc(v_input_1592_);
lean_inc(v_state_1591_);
lean_dec(v_reader_1590_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
uint8_t v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = 1;
if (v_isShared_1599_ == 0)
{
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_state_1591_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_input_1592_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_messageHead_1593_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_messageCount_1594_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_bodyBytesRead_1595_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v_headerBytesRead_1596_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*6, v___x_1600_);
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object* v_dir_1605_, lean_object* v_reader_1606_){
_start:
{
uint8_t v_dir_boxed_1607_; lean_object* v_res_1608_; 
v_dir_boxed_1607_ = lean_unbox(v_dir_1605_);
v_res_1608_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_1607_, v_reader_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1609_, lean_object* v_reader_1610_){
_start:
{
lean_object* v_messageHead_1611_; uint8_t v___x_1612_; 
v_messageHead_1611_ = lean_ctor_get(v_reader_1610_, 2);
v___x_1612_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1609_, v_messageHead_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1613_, lean_object* v_reader_1614_){
_start:
{
uint8_t v_dir_boxed_1615_; uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_dir_boxed_1615_ = lean_unbox(v_dir_1613_);
v_res_1616_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1615_, v_reader_1614_);
lean_dec_ref(v_reader_1614_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
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
