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
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
default: 
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim___redArg(lean_object* v_t_24_, lean_object* v_fixed_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_24_, v_fixed_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_fixed_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_fixed_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_28_, v_fixed_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim___redArg(lean_object* v_t_32_, lean_object* v_chunkedSize_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_32_, v_chunkedSize_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedSize_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_chunkedSize_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_36_, v_chunkedSize_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim___redArg(lean_object* v_t_40_, lean_object* v_chunkedBody_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_40_, v_chunkedBody_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_chunkedBody_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_chunkedBody_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_44_, v_chunkedBody_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim___redArg(lean_object* v_t_48_, lean_object* v_closeDelimited_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_48_, v_closeDelimited_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_BodyState_closeDelimited_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_closeDelimited_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Http_Protocol_H1_Reader_BodyState_ctorElim___redArg(v_t_52_, v_closeDelimited_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__1));
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_val_69_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_val_69_);
lean_dec_ref_known(v_x_66_, 1);
v___x_70_ = ((lean_object*)(l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___closed__3));
v___x_71_ = l_Std_Http_Chunk_instReprExtensionValue_repr___redArg(v_val_69_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_x_67_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1___boxed(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_x_74_, v_x_75_);
lean_dec(v_x_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_dec(v_x_77_);
return v_x_78_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_90_; 
v_head_80_ = lean_ctor_get(v_x_79_, 0);
v_tail_81_ = lean_ctor_get(v_x_79_, 1);
v_isSharedCheck_90_ = !lean_is_exclusive(v_x_79_);
if (v_isSharedCheck_90_ == 0)
{
v___x_83_ = v_x_79_;
v_isShared_84_ = v_isSharedCheck_90_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_head_80_);
lean_dec(v_x_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_90_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
lean_inc(v_x_77_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 5);
lean_ctor_set(v___x_83_, 1, v_x_77_);
lean_ctor_set(v___x_83_, 0, v_x_78_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_x_78_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_x_77_);
v___x_86_ = v_reuseFailAlloc_89_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_head_80_);
v_x_78_ = v___x_87_;
v_x_79_ = v_tail_81_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
lean_object* v___x_93_; 
lean_dec(v_x_92_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v_tail_94_; 
v_tail_94_ = lean_ctor_get(v_x_91_, 1);
if (lean_obj_tag(v_tail_94_) == 0)
{
lean_object* v_head_95_; 
lean_dec(v_x_92_);
v_head_95_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_95_);
lean_dec_ref_known(v_x_91_, 2);
return v_head_95_;
}
else
{
lean_object* v_head_96_; lean_object* v___x_97_; 
lean_inc(v_tail_94_);
v_head_96_ = lean_ctor_get(v_x_91_, 0);
lean_inc(v_head_96_);
lean_dec_ref_known(v_x_91_, 2);
v___x_97_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2_spec__4(v_x_92_, v_head_96_, v_tail_94_);
return v___x_97_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__0));
v___x_107_ = lean_string_length(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5, &l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__5);
v___x_109_ = lean_nat_to_int(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(lean_object* v_x_114_){
_start:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_139_; 
v_fst_115_ = lean_ctor_get(v_x_114_, 0);
v_snd_116_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_139_ == 0)
{
v___x_118_ = v_x_114_;
v_isShared_119_ = v_isSharedCheck_139_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_139_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = l_Std_Http_Chunk_instReprExtensionName_repr___redArg(v_fst_115_);
v___x_122_ = lean_box(0);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
lean_ctor_set(v___x_118_, 1, v___x_122_);
lean_ctor_set(v___x_118_, 0, v___x_121_);
v___x_124_ = v___x_118_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_138_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; 
v___x_125_ = l_Option_repr___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__1(v_snd_116_, v___x_120_);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_124_);
v___x_127_ = l_List_reverse___redArg(v___x_126_);
v___x_128_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3));
v___x_129_ = l_Std_Format_joinSep___at___00Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0_spec__2(v___x_127_, v___x_128_);
v___x_130_ = lean_obj_once(&l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6, &l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6_once, _init_l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__6);
v___x_131_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__7));
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_129_);
v___x_133_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__8));
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_130_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = 0;
v___x_137_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*1, v___x_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_dec(v_x_140_);
return v_x_141_;
}
else
{
lean_object* v_head_143_; lean_object* v_tail_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_154_; 
v_head_143_ = lean_ctor_get(v_x_142_, 0);
v_tail_144_ = lean_ctor_get(v_x_142_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_154_ == 0)
{
v___x_146_ = v_x_142_;
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_tail_144_);
lean_inc(v_head_143_);
lean_dec(v_x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_154_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
lean_inc(v_x_140_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 5);
lean_ctor_set(v___x_146_, 1, v_x_140_);
lean_ctor_set(v___x_146_, 0, v_x_141_);
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_x_141_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_x_140_);
v___x_149_ = v_reuseFailAlloc_153_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_143_);
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v_x_141_ = v___x_151_;
v_x_142_ = v_tail_144_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_dec(v_x_155_);
return v_x_156_;
}
else
{
lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_169_; 
v_head_158_ = lean_ctor_get(v_x_157_, 0);
v_tail_159_ = lean_ctor_get(v_x_157_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_169_ == 0)
{
v___x_161_ = v_x_157_;
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_tail_159_);
lean_inc(v_head_158_);
lean_dec(v_x_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
lean_inc(v_x_155_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 5);
lean_ctor_set(v___x_161_, 1, v_x_155_);
lean_ctor_set(v___x_161_, 0, v_x_156_);
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_x_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_x_155_);
v___x_164_ = v_reuseFailAlloc_168_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_158_);
v___x_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4_spec__7(v_x_155_, v___x_166_, v_tail_159_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
if (lean_obj_tag(v_x_170_) == 0)
{
lean_object* v___x_172_; 
lean_dec(v_x_171_);
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v_tail_173_; 
v_tail_173_ = lean_ctor_get(v_x_170_, 1);
if (lean_obj_tag(v_tail_173_) == 0)
{
lean_object* v_head_174_; lean_object* v___x_175_; 
lean_dec(v_x_171_);
v_head_174_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_head_174_);
lean_dec_ref_known(v_x_170_, 2);
v___x_175_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_174_);
return v___x_175_;
}
else
{
lean_object* v_head_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_inc(v_tail_173_);
v_head_176_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_head_176_);
lean_dec_ref_known(v_x_170_, 2);
v___x_177_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_head_176_);
v___x_178_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1_spec__4(v_x_171_, v___x_177_, v_tail_173_);
return v___x_178_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__0));
v___x_182_ = lean_string_length(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2, &l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2_once, _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__2);
v___x_184_ = lean_nat_to_int(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(lean_object* v_xs_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = lean_array_get_size(v_xs_192_);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_nat_dec_eq(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_196_ = lean_array_to_list(v_xs_192_);
v___x_197_ = ((lean_object*)(l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg___closed__3));
v___x_198_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__1(v___x_196_, v___x_197_);
v___x_199_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__3);
v___x_200_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__4));
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___x_198_);
v___x_202_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__5));
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_199_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = l_Std_Format_fill(v___x_204_);
return v___x_205_;
}
else
{
lean_object* v___x_206_; 
lean_dec_ref(v_xs_192_);
v___x_206_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0___closed__7));
return v___x_206_;
}
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(lean_object* v_x_229_, lean_object* v_prec_230_){
_start:
{
lean_object* v___y_232_; lean_object* v___y_239_; 
switch(lean_obj_tag(v_x_229_))
{
case 0:
{
lean_object* v_remaining_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_265_; 
v_remaining_245_ = lean_ctor_get(v_x_229_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_265_ == 0)
{
v___x_247_ = v_x_229_;
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_remaining_245_);
lean_dec(v_x_229_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_265_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___y_250_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_unsigned_to_nat(1024u);
v___x_262_ = lean_nat_dec_le(v___x_261_, v_prec_230_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
v___x_263_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_250_ = v___x_263_;
goto v___jp_249_;
}
else
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_250_ = v___x_264_;
goto v___jp_249_;
}
v___jp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_251_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__6));
v___x_252_ = l_Nat_reprFast(v_remaining_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 3);
lean_ctor_set(v___x_247_, 0, v___x_252_);
v___x_254_ = v___x_247_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_260_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_251_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_inc(v___y_250_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___y_250_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
v___x_259_ = l_Repr_addAppParen(v___x_258_, v_prec_230_);
return v___x_259_;
}
}
}
}
case 1:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(1024u);
v___x_267_ = lean_nat_dec_le(v___x_266_, v_prec_230_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_232_ = v___x_268_;
goto v___jp_231_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_232_ = v___x_269_;
goto v___jp_231_;
}
}
case 2:
{
lean_object* v_ext_270_; lean_object* v_remaining_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_295_; 
v_ext_270_ = lean_ctor_get(v_x_229_, 0);
v_remaining_271_ = lean_ctor_get(v_x_229_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_295_ == 0)
{
v___x_273_ = v_x_229_;
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_remaining_271_);
lean_inc(v_ext_270_);
lean_dec(v_x_229_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___y_276_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1024u);
v___x_292_ = lean_nat_dec_le(v___x_291_, v_prec_230_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_276_ = v___x_293_;
goto v___jp_275_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_276_ = v___x_294_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_277_ = lean_box(1);
v___x_278_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__11));
v___x_279_ = l_Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0(v_ext_270_);
if (v_isShared_274_ == 0)
{
lean_ctor_set_tag(v___x_273_, 5);
lean_ctor_set(v___x_273_, 1, v___x_279_);
lean_ctor_set(v___x_273_, 0, v___x_278_);
v___x_281_ = v___x_273_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_279_);
v___x_281_ = v_reuseFailAlloc_290_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_277_);
v___x_283_ = l_Nat_reprFast(v_remaining_271_);
v___x_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_inc(v___y_276_);
v___x_286_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_286_, 0, v___y_276_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = 0;
v___x_288_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*1, v___x_287_);
v___x_289_ = l_Repr_addAppParen(v___x_288_, v_prec_230_);
return v___x_289_;
}
}
}
}
default: 
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(1024u);
v___x_297_ = lean_nat_dec_le(v___x_296_, v_prec_230_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_239_ = v___x_298_;
goto v___jp_238_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_239_ = v___x_299_;
goto v___jp_238_;
}
}
}
v___jp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_233_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__1));
lean_inc(v___y_232_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___y_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = 0;
v___x_236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_235_);
v___x_237_ = l_Repr_addAppParen(v___x_236_, v_prec_230_);
return v___x_237_;
}
v___jp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__3));
lean_inc(v___y_239_);
v___x_241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_241_, 0, v___y_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = l_Repr_addAppParen(v___x_243_, v_prec_230_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___boxed(lean_object* v_x_300_, lean_object* v_prec_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_x_300_, v_prec_301_);
lean_dec(v_prec_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__2(lean_object* v_a_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_nat_to_int(v_a_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___redArg(v_x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0___boxed(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Prod_repr___at___00Array_repr___at___00Std_Http_Protocol_H1_Reader_instReprBodyState_repr_spec__0_spec__0(v_x_308_, v_x_309_);
lean_dec(v_x_309_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
if (lean_obj_tag(v_x_314_) == 0)
{
uint8_t v___x_315_; 
v___x_315_ = 1;
return v___x_315_;
}
else
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
}
else
{
if (lean_obj_tag(v_x_314_) == 0)
{
uint8_t v___x_317_; 
v___x_317_ = 0;
return v___x_317_;
}
else
{
lean_object* v_val_318_; lean_object* v_val_319_; uint8_t v___x_320_; 
v_val_318_ = lean_ctor_get(v_x_313_, 0);
v_val_319_ = lean_ctor_get(v_x_314_, 0);
v___x_320_ = l_Std_Http_Chunk_instBEqExtensionValue_beq(v_val_318_, v_val_319_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_x_321_, v_x_322_);
lean_dec(v_x_322_);
lean_dec(v_x_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(lean_object* v_xs_325_, lean_object* v_ys_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_zero_328_; uint8_t v_isZero_329_; 
v_zero_328_ = lean_unsigned_to_nat(0u);
v_isZero_329_ = lean_nat_dec_eq(v_x_327_, v_zero_328_);
if (v_isZero_329_ == 1)
{
lean_dec(v_x_327_);
return v_isZero_329_;
}
else
{
lean_object* v_one_330_; lean_object* v_n_331_; lean_object* v___x_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_335_; lean_object* v_fst_336_; lean_object* v_snd_337_; uint8_t v___x_338_; 
v_one_330_ = lean_unsigned_to_nat(1u);
v_n_331_ = lean_nat_sub(v_x_327_, v_one_330_);
lean_dec(v_x_327_);
v___x_332_ = lean_array_fget_borrowed(v_xs_325_, v_n_331_);
v_fst_333_ = lean_ctor_get(v___x_332_, 0);
v_snd_334_ = lean_ctor_get(v___x_332_, 1);
v___x_335_ = lean_array_fget_borrowed(v_ys_326_, v_n_331_);
v_fst_336_ = lean_ctor_get(v___x_335_, 0);
v_snd_337_ = lean_ctor_get(v___x_335_, 1);
v___x_338_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_fst_333_, v_fst_336_);
if (v___x_338_ == 0)
{
lean_dec(v_n_331_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_snd_334_, v_snd_337_);
if (v___x_339_ == 0)
{
lean_dec(v_n_331_);
return v___x_339_;
}
else
{
v_x_327_ = v_n_331_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object* v_xs_341_, lean_object* v_ys_342_, lean_object* v_x_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_341_, v_ys_342_, v_x_343_);
lean_dec_ref(v_ys_342_);
lean_dec_ref(v_xs_341_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
switch(lean_obj_tag(v_x_346_))
{
case 0:
{
if (lean_obj_tag(v_x_347_) == 0)
{
lean_object* v_remaining_348_; lean_object* v_remaining_349_; uint8_t v___x_350_; 
v_remaining_348_ = lean_ctor_get(v_x_346_, 0);
v_remaining_349_ = lean_ctor_get(v_x_347_, 0);
v___x_350_ = lean_nat_dec_eq(v_remaining_348_, v_remaining_349_);
return v___x_350_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 0;
return v___x_351_;
}
}
case 1:
{
if (lean_obj_tag(v_x_347_) == 1)
{
uint8_t v___x_352_; 
v___x_352_ = 1;
return v___x_352_;
}
else
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
}
case 2:
{
if (lean_obj_tag(v_x_347_) == 2)
{
lean_object* v_ext_354_; lean_object* v_remaining_355_; lean_object* v_ext_356_; lean_object* v_remaining_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v_ext_354_ = lean_ctor_get(v_x_346_, 0);
v_remaining_355_ = lean_ctor_get(v_x_346_, 1);
v_ext_356_ = lean_ctor_get(v_x_347_, 0);
v_remaining_357_ = lean_ctor_get(v_x_347_, 1);
v___x_358_ = lean_array_get_size(v_ext_354_);
v___x_359_ = lean_array_get_size(v_ext_356_);
v___x_360_ = lean_nat_dec_eq(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_ext_354_, v_ext_356_, v___x_358_);
if (v___x_361_ == 0)
{
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = lean_nat_dec_eq(v_remaining_355_, v_remaining_357_);
return v___x_362_;
}
}
}
else
{
uint8_t v___x_363_; 
v___x_363_ = 0;
return v___x_363_;
}
}
default: 
{
if (lean_obj_tag(v_x_347_) == 3)
{
uint8_t v___x_364_; 
v___x_364_ = 1;
return v___x_364_;
}
else
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq___boxed(lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_366_, v_x_367_);
lean_dec(v_x_367_);
lean_dec(v_x_366_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object* v_xs_370_, lean_object* v_ys_371_, lean_object* v_hsz_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_370_, v_ys_371_, v_x_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object* v_xs_376_, lean_object* v_ys_377_, lean_object* v_hsz_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(v_xs_376_, v_ys_377_, v_hsz_378_, v_x_379_, v_x_380_);
lean_dec_ref(v_ys_377_);
lean_dec_ref(v_xs_376_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_obj_tag_nat(v_x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg___boxed(lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(v_x_387_);
lean_dec(v_x_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(uint8_t v_dir_389_, lean_object* v_x_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_tag_nat(v_x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___boxed(lean_object* v_dir_392_, lean_object* v_x_393_){
_start:
{
uint8_t v_dir_boxed_394_; lean_object* v_res_395_; 
v_dir_boxed_394_ = lean_unbox(v_dir_392_);
v_res_395_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(v_dir_boxed_394_, v_x_393_);
lean_dec(v_x_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(lean_object* v_t_396_, lean_object* v_k_397_){
_start:
{
switch(lean_obj_tag(v_t_396_))
{
case 1:
{
lean_object* v_a_398_; lean_object* v___x_399_; 
v_a_398_ = lean_ctor_get(v_t_396_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v_t_396_, 1);
v___x_399_ = lean_apply_1(v_k_397_, v_a_398_);
return v___x_399_;
}
case 2:
{
lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_400_ = lean_ctor_get(v_t_396_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v_t_396_, 1);
v___x_401_ = lean_apply_1(v_k_397_, v_a_400_);
return v___x_401_;
}
case 3:
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v_t_396_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v_t_396_, 1);
v___x_403_ = lean_apply_1(v_k_397_, v_a_402_);
return v___x_403_;
}
case 7:
{
lean_object* v_error_404_; lean_object* v___x_405_; 
v_error_404_ = lean_ctor_get(v_t_396_, 0);
lean_inc(v_error_404_);
lean_dec_ref_known(v_t_396_, 1);
v___x_405_ = lean_apply_1(v_k_397_, v_error_404_);
return v___x_405_;
}
default: 
{
lean_dec(v_t_396_);
return v_k_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t v_dir_406_, lean_object* v_motive_407_, lean_object* v_ctorIdx_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_k_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_409_, v_k_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object* v_dir_413_, lean_object* v_motive_414_, lean_object* v_ctorIdx_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_k_418_){
_start:
{
uint8_t v_dir_boxed_419_; lean_object* v_res_420_; 
v_dir_boxed_419_ = lean_unbox(v_dir_413_);
v_res_420_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_boxed_419_, v_motive_414_, v_ctorIdx_415_, v_t_416_, v_h_417_, v_k_418_);
lean_dec(v_ctorIdx_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object* v_t_421_, lean_object* v_needStartLine_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_421_, v_needStartLine_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t v_dir_424_, lean_object* v_motive_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_needStartLine_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_426_, v_needStartLine_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object* v_dir_430_, lean_object* v_motive_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_needStartLine_434_){
_start:
{
uint8_t v_dir_boxed_435_; lean_object* v_res_436_; 
v_dir_boxed_435_ = lean_unbox(v_dir_430_);
v_res_436_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_boxed_435_, v_motive_431_, v_t_432_, v_h_433_, v_needStartLine_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object* v_t_437_, lean_object* v_needHeader_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_437_, v_needHeader_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t v_dir_440_, lean_object* v_motive_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_needHeader_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_442_, v_needHeader_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object* v_dir_446_, lean_object* v_motive_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_needHeader_450_){
_start:
{
uint8_t v_dir_boxed_451_; lean_object* v_res_452_; 
v_dir_boxed_451_ = lean_unbox(v_dir_446_);
v_res_452_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_boxed_451_, v_motive_447_, v_t_448_, v_h_449_, v_needHeader_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object* v_t_453_, lean_object* v_readBody_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_453_, v_readBody_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t v_dir_456_, lean_object* v_motive_457_, lean_object* v_t_458_, lean_object* v_h_459_, lean_object* v_readBody_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_458_, v_readBody_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object* v_dir_462_, lean_object* v_motive_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_readBody_466_){
_start:
{
uint8_t v_dir_boxed_467_; lean_object* v_res_468_; 
v_dir_boxed_467_ = lean_unbox(v_dir_462_);
v_res_468_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_boxed_467_, v_motive_463_, v_t_464_, v_h_465_, v_readBody_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object* v_t_469_, lean_object* v_continue_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_469_, v_continue_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t v_dir_472_, lean_object* v_motive_473_, lean_object* v_t_474_, lean_object* v_h_475_, lean_object* v_continue_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_474_, v_continue_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___boxed(lean_object* v_dir_478_, lean_object* v_motive_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_continue_482_){
_start:
{
uint8_t v_dir_boxed_483_; lean_object* v_res_484_; 
v_dir_boxed_483_ = lean_unbox(v_dir_478_);
v_res_484_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(v_dir_boxed_483_, v_motive_479_, v_t_480_, v_h_481_, v_continue_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___redArg(lean_object* v_t_485_, lean_object* v_pending_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_485_, v_pending_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t v_dir_488_, lean_object* v_motive_489_, lean_object* v_t_490_, lean_object* v_h_491_, lean_object* v_pending_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_490_, v_pending_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object* v_dir_494_, lean_object* v_motive_495_, lean_object* v_t_496_, lean_object* v_h_497_, lean_object* v_pending_498_){
_start:
{
uint8_t v_dir_boxed_499_; lean_object* v_res_500_; 
v_dir_boxed_499_ = lean_unbox(v_dir_494_);
v_res_500_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_boxed_499_, v_motive_495_, v_t_496_, v_h_497_, v_pending_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object* v_t_501_, lean_object* v_complete_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_501_, v_complete_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t v_dir_504_, lean_object* v_motive_505_, lean_object* v_t_506_, lean_object* v_h_507_, lean_object* v_complete_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_506_, v_complete_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object* v_dir_510_, lean_object* v_motive_511_, lean_object* v_t_512_, lean_object* v_h_513_, lean_object* v_complete_514_){
_start:
{
uint8_t v_dir_boxed_515_; lean_object* v_res_516_; 
v_dir_boxed_515_ = lean_unbox(v_dir_510_);
v_res_516_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_boxed_515_, v_motive_511_, v_t_512_, v_h_513_, v_complete_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object* v_t_517_, lean_object* v_closed_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_517_, v_closed_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t v_dir_520_, lean_object* v_motive_521_, lean_object* v_t_522_, lean_object* v_h_523_, lean_object* v_closed_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_522_, v_closed_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object* v_dir_526_, lean_object* v_motive_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_closed_530_){
_start:
{
uint8_t v_dir_boxed_531_; lean_object* v_res_532_; 
v_dir_boxed_531_ = lean_unbox(v_dir_526_);
v_res_532_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_boxed_531_, v_motive_527_, v_t_528_, v_h_529_, v_closed_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(lean_object* v_t_533_, lean_object* v_failed_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_533_, v_failed_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim(uint8_t v_dir_536_, lean_object* v_motive_537_, lean_object* v_t_538_, lean_object* v_h_539_, lean_object* v_failed_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_538_, v_failed_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(lean_object* v_dir_542_, lean_object* v_motive_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_failed_546_){
_start:
{
uint8_t v_dir_boxed_547_; lean_object* v_res_548_; 
v_dir_boxed_547_ = lean_unbox(v_dir_542_);
v_res_548_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(v_dir_boxed_547_, v_motive_543_, v_t_544_, v_h_545_, v_failed_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg(){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_box(0);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object* v___dummy_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = lean_box(0);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_555_){
_start:
{
uint8_t v_dir_boxed_556_; lean_object* v_res_557_; 
v_dir_boxed_556_ = lean_unbox(v_dir_555_);
v_res_557_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg(){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_box(0);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object* v___dummy_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_564_){
_start:
{
uint8_t v_a_11__boxed_565_; lean_object* v_res_566_; 
v_a_11__boxed_565_ = lean_unbox(v_a_564_);
v_res_566_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_11__boxed_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_603_, lean_object* v_prec_604_){
_start:
{
lean_object* v___y_606_; lean_object* v___y_613_; lean_object* v___y_620_; lean_object* v___y_627_; 
switch(lean_obj_tag(v_x_603_))
{
case 0:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(1024u);
v___x_634_ = lean_nat_dec_le(v___x_633_, v_prec_604_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_627_ = v___x_635_;
goto v___jp_626_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_627_ = v___x_636_;
goto v___jp_626_;
}
}
case 1:
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_657_; 
v_a_637_ = lean_ctor_get(v_x_603_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_657_ == 0)
{
v___x_639_ = v_x_603_;
v_isShared_640_ = v_isSharedCheck_657_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v_x_603_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_657_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___y_642_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1024u);
v___x_654_ = lean_nat_dec_le(v___x_653_, v_prec_604_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_642_ = v___x_655_;
goto v___jp_641_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_642_ = v___x_656_;
goto v___jp_641_;
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_643_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_644_ = l_Nat_reprFast(v_a_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 3);
lean_ctor_set(v___x_639_, 0, v___x_644_);
v___x_646_ = v___x_639_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_652_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_643_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_inc(v___y_642_);
v___x_648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_642_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = 0;
v___x_650_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v___x_649_);
v___x_651_ = l_Repr_addAppParen(v___x_650_, v_prec_604_);
return v___x_651_;
}
}
}
}
case 2:
{
lean_object* v_a_658_; lean_object* v___y_660_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_a_658_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_x_603_, 1);
v___x_669_ = lean_unsigned_to_nat(1024u);
v___x_670_ = lean_nat_dec_le(v___x_669_, v_prec_604_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_660_ = v___x_671_;
goto v___jp_659_;
}
else
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_660_ = v___x_672_;
goto v___jp_659_;
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_661_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_662_ = lean_unsigned_to_nat(1024u);
v___x_663_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_658_, v___x_662_);
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_661_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
lean_inc(v___y_660_);
v___x_665_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_665_, 0, v___y_660_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = 0;
v___x_667_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*1, v___x_666_);
v___x_668_ = l_Repr_addAppParen(v___x_667_, v_prec_604_);
return v___x_668_;
}
}
case 3:
{
lean_object* v_a_673_; lean_object* v___x_674_; lean_object* v___y_676_; uint8_t v___x_684_; 
v_a_673_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v_x_603_, 1);
v___x_674_ = lean_unsigned_to_nat(1024u);
v___x_684_ = lean_nat_dec_le(v___x_674_, v_prec_604_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_676_ = v___x_685_;
goto v___jp_675_;
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_676_ = v___x_686_;
goto v___jp_675_;
}
v___jp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_677_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_678_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_673_, v___x_674_);
v___x_679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
lean_inc(v___y_676_);
v___x_680_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_680_, 0, v___y_676_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = 0;
v___x_682_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*1, v___x_681_);
v___x_683_ = l_Repr_addAppParen(v___x_682_, v_prec_604_);
return v___x_683_;
}
}
case 4:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(1024u);
v___x_688_ = lean_nat_dec_le(v___x_687_, v_prec_604_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_620_ = v___x_689_;
goto v___jp_619_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_620_ = v___x_690_;
goto v___jp_619_;
}
}
case 5:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(1024u);
v___x_692_ = lean_nat_dec_le(v___x_691_, v_prec_604_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_613_ = v___x_693_;
goto v___jp_612_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_613_ = v___x_694_;
goto v___jp_612_;
}
}
case 6:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(1024u);
v___x_696_ = lean_nat_dec_le(v___x_695_, v_prec_604_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_606_ = v___x_697_;
goto v___jp_605_;
}
else
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_606_ = v___x_698_;
goto v___jp_605_;
}
}
default: 
{
lean_object* v_error_699_; lean_object* v___y_701_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_error_699_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_error_699_);
lean_dec_ref_known(v_x_603_, 1);
v___x_710_ = lean_unsigned_to_nat(1024u);
v___x_711_ = lean_nat_dec_le(v___x_710_, v_prec_604_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_701_ = v___x_712_;
goto v___jp_700_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_701_ = v___x_713_;
goto v___jp_700_;
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_702_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19));
v___x_703_ = lean_unsigned_to_nat(1024u);
v___x_704_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_699_, v___x_703_);
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_702_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
lean_inc(v___y_701_);
v___x_706_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_706_, 0, v___y_701_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = 0;
v___x_708_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*1, v___x_707_);
v___x_709_ = l_Repr_addAppParen(v___x_708_, v_prec_604_);
return v___x_709_;
}
}
}
v___jp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_607_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_606_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___y_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = 0;
v___x_610_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*1, v___x_609_);
v___x_611_ = l_Repr_addAppParen(v___x_610_, v_prec_604_);
return v___x_611_;
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_614_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_613_);
v___x_615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_615_, 0, v___y_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = 0;
v___x_617_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*1, v___x_616_);
v___x_618_ = l_Repr_addAppParen(v___x_617_, v_prec_604_);
return v___x_618_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_621_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_620_);
v___x_622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_622_, 0, v___y_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = 0;
v___x_624_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*1, v___x_623_);
v___x_625_ = l_Repr_addAppParen(v___x_624_, v_prec_604_);
return v___x_625_;
}
v___jp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_627_);
v___x_629_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_629_, 0, v___y_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = 0;
v___x_631_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*1, v___x_630_);
v___x_632_ = l_Repr_addAppParen(v___x_631_, v_prec_604_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_714_, lean_object* v_prec_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_714_, v_prec_715_);
lean_dec(v_prec_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_717_, lean_object* v_x_718_, lean_object* v_prec_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_718_, v_prec_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_721_, lean_object* v_x_722_, lean_object* v_prec_723_){
_start:
{
uint8_t v_dir_876__boxed_724_; lean_object* v_res_725_; 
v_dir_876__boxed_724_ = lean_unbox(v_dir_721_);
v_res_725_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_876__boxed_724_, v_x_722_, v_prec_723_);
lean_dec(v_prec_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(v_dir_726_);
v___x_728_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_729_){
_start:
{
uint8_t v_dir_5__boxed_730_; lean_object* v_res_731_; 
v_dir_5__boxed_730_ = lean_unbox(v_dir_729_);
v_res_731_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_730_);
return v_res_731_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
switch(lean_obj_tag(v_x_732_))
{
case 0:
{
if (lean_obj_tag(v_x_733_) == 0)
{
uint8_t v___x_734_; 
v___x_734_ = 1;
return v___x_734_;
}
else
{
uint8_t v___x_735_; 
v___x_735_ = 0;
return v___x_735_;
}
}
case 1:
{
if (lean_obj_tag(v_x_733_) == 1)
{
lean_object* v_a_736_; lean_object* v_a_737_; uint8_t v___x_738_; 
v_a_736_ = lean_ctor_get(v_x_732_, 0);
v_a_737_ = lean_ctor_get(v_x_733_, 0);
v___x_738_ = lean_nat_dec_eq(v_a_736_, v_a_737_);
return v___x_738_;
}
else
{
uint8_t v___x_739_; 
v___x_739_ = 0;
return v___x_739_;
}
}
case 2:
{
if (lean_obj_tag(v_x_733_) == 2)
{
lean_object* v_a_740_; lean_object* v_a_741_; uint8_t v___x_742_; 
v_a_740_ = lean_ctor_get(v_x_732_, 0);
v_a_741_ = lean_ctor_get(v_x_733_, 0);
v___x_742_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_740_, v_a_741_);
return v___x_742_;
}
else
{
uint8_t v___x_743_; 
v___x_743_ = 0;
return v___x_743_;
}
}
case 3:
{
if (lean_obj_tag(v_x_733_) == 3)
{
lean_object* v_a_744_; lean_object* v_a_745_; 
v_a_744_ = lean_ctor_get(v_x_732_, 0);
v_a_745_ = lean_ctor_get(v_x_733_, 0);
v_x_732_ = v_a_744_;
v_x_733_ = v_a_745_;
goto _start;
}
else
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
case 4:
{
if (lean_obj_tag(v_x_733_) == 4)
{
uint8_t v___x_748_; 
v___x_748_ = 1;
return v___x_748_;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = 0;
return v___x_749_;
}
}
case 5:
{
if (lean_obj_tag(v_x_733_) == 5)
{
uint8_t v___x_750_; 
v___x_750_ = 1;
return v___x_750_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = 0;
return v___x_751_;
}
}
case 6:
{
if (lean_obj_tag(v_x_733_) == 6)
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
default: 
{
if (lean_obj_tag(v_x_733_) == 7)
{
lean_object* v_error_754_; lean_object* v_error_755_; uint8_t v___x_756_; 
v_error_754_ = lean_ctor_get(v_x_732_, 0);
v_error_755_ = lean_ctor_get(v_x_733_, 0);
v___x_756_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_error_754_, v_error_755_);
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
uint8_t v_res_760_; lean_object* v_r_761_; 
v_res_760_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_758_, v_x_759_);
lean_dec(v_x_759_);
lean_dec(v_x_758_);
v_r_761_ = lean_box(v_res_760_);
return v_r_761_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_762_, lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_763_, v_x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_766_, lean_object* v_x_767_, lean_object* v_x_768_){
_start:
{
uint8_t v_dir_183__boxed_769_; uint8_t v_res_770_; lean_object* v_r_771_; 
v_dir_183__boxed_769_ = lean_unbox(v_dir_766_);
v_res_770_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_183__boxed_769_, v_x_767_, v_x_768_);
lean_dec(v_x_768_);
lean_dec(v_x_767_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_box(v_dir_772_);
v___x_774_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_775_){
_start:
{
uint8_t v_dir_5__boxed_776_; lean_object* v_res_777_; 
v_dir_5__boxed_776_ = lean_unbox(v_dir_775_);
v_res_777_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_776_);
return v_res_777_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_778_){
_start:
{
lean_object* v_state_779_; 
v_state_779_ = lean_ctor_get(v_reader_778_, 0);
if (lean_obj_tag(v_state_779_) == 6)
{
uint8_t v___x_780_; 
v___x_780_ = 1;
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = 0;
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_782_);
lean_dec_ref(v_reader_782_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_785_, lean_object* v_reader_786_){
_start:
{
lean_object* v_state_787_; 
v_state_787_ = lean_ctor_get(v_reader_786_, 0);
if (lean_obj_tag(v_state_787_) == 6)
{
uint8_t v___x_788_; 
v___x_788_ = 1;
return v___x_788_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = 0;
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_790_, lean_object* v_reader_791_){
_start:
{
uint8_t v_dir_boxed_792_; uint8_t v_res_793_; lean_object* v_r_794_; 
v_dir_boxed_792_ = lean_unbox(v_dir_790_);
v_res_793_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_792_, v_reader_791_);
lean_dec_ref(v_reader_791_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_795_){
_start:
{
lean_object* v_state_796_; 
v_state_796_ = lean_ctor_get(v_reader_795_, 0);
if (lean_obj_tag(v_state_796_) == 5)
{
uint8_t v___x_797_; 
v___x_797_ = 1;
return v___x_797_;
}
else
{
uint8_t v___x_798_; 
v___x_798_ = 0;
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_799_);
lean_dec_ref(v_reader_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_802_, lean_object* v_reader_803_){
_start:
{
lean_object* v_state_804_; 
v_state_804_ = lean_ctor_get(v_reader_803_, 0);
if (lean_obj_tag(v_state_804_) == 5)
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
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_807_, lean_object* v_reader_808_){
_start:
{
uint8_t v_dir_boxed_809_; uint8_t v_res_810_; lean_object* v_r_811_; 
v_dir_boxed_809_ = lean_unbox(v_dir_807_);
v_res_810_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_809_, v_reader_808_);
lean_dec_ref(v_reader_808_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object* v_reader_812_){
_start:
{
lean_object* v_state_813_; 
v_state_813_ = lean_ctor_get(v_reader_812_, 0);
if (lean_obj_tag(v_state_813_) == 7)
{
uint8_t v___x_814_; 
v___x_814_ = 1;
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object* v_reader_816_){
_start:
{
uint8_t v_res_817_; lean_object* v_r_818_; 
v_res_817_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_816_);
lean_dec_ref(v_reader_816_);
v_r_818_ = lean_box(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t v_dir_819_, lean_object* v_reader_820_){
_start:
{
lean_object* v_state_821_; 
v_state_821_ = lean_ctor_get(v_reader_820_, 0);
if (lean_obj_tag(v_state_821_) == 7)
{
uint8_t v___x_822_; 
v___x_822_ = 1;
return v___x_822_;
}
else
{
uint8_t v___x_823_; 
v___x_823_ = 0;
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object* v_dir_824_, lean_object* v_reader_825_){
_start:
{
uint8_t v_dir_boxed_826_; uint8_t v_res_827_; lean_object* v_r_828_; 
v_dir_boxed_826_ = lean_unbox(v_dir_824_);
v_res_827_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_826_, v_reader_825_);
lean_dec_ref(v_reader_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_829_, lean_object* v_reader_830_){
_start:
{
lean_object* v_input_831_; lean_object* v_state_832_; lean_object* v_messageHead_833_; lean_object* v_messageCount_834_; lean_object* v_bodyBytesRead_835_; lean_object* v_headerBytesRead_836_; uint8_t v_noMoreInput_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_858_; 
v_input_831_ = lean_ctor_get(v_reader_830_, 1);
v_state_832_ = lean_ctor_get(v_reader_830_, 0);
v_messageHead_833_ = lean_ctor_get(v_reader_830_, 2);
v_messageCount_834_ = lean_ctor_get(v_reader_830_, 3);
v_bodyBytesRead_835_ = lean_ctor_get(v_reader_830_, 4);
v_headerBytesRead_836_ = lean_ctor_get(v_reader_830_, 5);
v_noMoreInput_837_ = lean_ctor_get_uint8(v_reader_830_, sizeof(void*)*6);
v_isSharedCheck_858_ = !lean_is_exclusive(v_reader_830_);
if (v_isSharedCheck_858_ == 0)
{
v___x_839_ = v_reader_830_;
v_isShared_840_ = v_isSharedCheck_858_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_headerBytesRead_836_);
lean_inc(v_bodyBytesRead_835_);
lean_inc(v_messageCount_834_);
lean_inc(v_messageHead_833_);
lean_inc(v_input_831_);
lean_inc(v_state_832_);
lean_dec(v_reader_830_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_858_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_array_841_; lean_object* v_idx_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_array_841_ = lean_ctor_get(v_input_831_, 0);
lean_inc_ref(v_array_841_);
v_idx_842_ = lean_ctor_get(v_input_831_, 1);
lean_inc(v_idx_842_);
lean_dec_ref(v_input_831_);
v___x_843_ = lean_byte_array_size(v_array_841_);
v___x_844_ = lean_nat_dec_le(v___x_843_, v_idx_842_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_845_ = l_ByteArray_extract(v_array_841_, v_idx_842_, v___x_843_);
lean_dec_ref(v_array_841_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_byte_array_size(v___x_845_);
v___x_848_ = lean_byte_array_size(v_data_829_);
v___x_849_ = lean_byte_array_copy_slice(v_data_829_, v___x_846_, v___x_845_, v___x_847_, v___x_848_, v___x_844_);
lean_dec_ref(v_data_829_);
v___x_850_ = l_ByteArray_mkIterator(v___x_849_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_850_);
v___x_852_ = v___x_839_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_state_832_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_messageHead_833_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_messageCount_834_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v_bodyBytesRead_835_);
lean_ctor_set(v_reuseFailAlloc_853_, 5, v_headerBytesRead_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_853_, sizeof(void*)*6, v_noMoreInput_837_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
else
{
lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_idx_842_);
lean_dec_ref(v_array_841_);
v___x_854_ = l_ByteArray_mkIterator(v_data_829_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_854_);
v___x_856_ = v___x_839_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_state_832_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_messageHead_833_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_messageCount_834_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_bodyBytesRead_835_);
lean_ctor_set(v_reuseFailAlloc_857_, 5, v_headerBytesRead_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_857_, sizeof(void*)*6, v_noMoreInput_837_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_859_, lean_object* v_data_860_, lean_object* v_reader_861_){
_start:
{
lean_object* v_input_862_; lean_object* v_state_863_; lean_object* v_messageHead_864_; lean_object* v_messageCount_865_; lean_object* v_bodyBytesRead_866_; lean_object* v_headerBytesRead_867_; uint8_t v_noMoreInput_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_889_; 
v_input_862_ = lean_ctor_get(v_reader_861_, 1);
v_state_863_ = lean_ctor_get(v_reader_861_, 0);
v_messageHead_864_ = lean_ctor_get(v_reader_861_, 2);
v_messageCount_865_ = lean_ctor_get(v_reader_861_, 3);
v_bodyBytesRead_866_ = lean_ctor_get(v_reader_861_, 4);
v_headerBytesRead_867_ = lean_ctor_get(v_reader_861_, 5);
v_noMoreInput_868_ = lean_ctor_get_uint8(v_reader_861_, sizeof(void*)*6);
v_isSharedCheck_889_ = !lean_is_exclusive(v_reader_861_);
if (v_isSharedCheck_889_ == 0)
{
v___x_870_ = v_reader_861_;
v_isShared_871_ = v_isSharedCheck_889_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_headerBytesRead_867_);
lean_inc(v_bodyBytesRead_866_);
lean_inc(v_messageCount_865_);
lean_inc(v_messageHead_864_);
lean_inc(v_input_862_);
lean_inc(v_state_863_);
lean_dec(v_reader_861_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_889_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_array_872_; lean_object* v_idx_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_array_872_ = lean_ctor_get(v_input_862_, 0);
lean_inc_ref(v_array_872_);
v_idx_873_ = lean_ctor_get(v_input_862_, 1);
lean_inc(v_idx_873_);
lean_dec_ref(v_input_862_);
v___x_874_ = lean_byte_array_size(v_array_872_);
v___x_875_ = lean_nat_dec_le(v___x_874_, v_idx_873_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_876_ = l_ByteArray_extract(v_array_872_, v_idx_873_, v___x_874_);
lean_dec_ref(v_array_872_);
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_byte_array_size(v___x_876_);
v___x_879_ = lean_byte_array_size(v_data_860_);
v___x_880_ = lean_byte_array_copy_slice(v_data_860_, v___x_877_, v___x_876_, v___x_878_, v___x_879_, v___x_875_);
lean_dec_ref(v_data_860_);
v___x_881_ = l_ByteArray_mkIterator(v___x_880_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_881_);
v___x_883_ = v___x_870_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_state_863_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_messageHead_864_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_messageCount_865_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v_bodyBytesRead_866_);
lean_ctor_set(v_reuseFailAlloc_884_, 5, v_headerBytesRead_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_884_, sizeof(void*)*6, v_noMoreInput_868_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v___x_885_; lean_object* v___x_887_; 
lean_dec(v_idx_873_);
lean_dec_ref(v_array_872_);
v___x_885_ = l_ByteArray_mkIterator(v_data_860_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_885_);
v___x_887_ = v___x_870_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_state_863_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_messageHead_864_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_messageCount_865_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_bodyBytesRead_866_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_headerBytesRead_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*6, v_noMoreInput_868_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_890_, lean_object* v_data_891_, lean_object* v_reader_892_){
_start:
{
uint8_t v_dir_boxed_893_; lean_object* v_res_894_; 
v_dir_boxed_893_ = lean_unbox(v_dir_890_);
v_res_894_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_893_, v_data_891_, v_reader_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_895_, lean_object* v_reader_896_){
_start:
{
lean_object* v_state_897_; lean_object* v_messageHead_898_; lean_object* v_messageCount_899_; lean_object* v_bodyBytesRead_900_; lean_object* v_headerBytesRead_901_; uint8_t v_noMoreInput_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
v_state_897_ = lean_ctor_get(v_reader_896_, 0);
v_messageHead_898_ = lean_ctor_get(v_reader_896_, 2);
v_messageCount_899_ = lean_ctor_get(v_reader_896_, 3);
v_bodyBytesRead_900_ = lean_ctor_get(v_reader_896_, 4);
v_headerBytesRead_901_ = lean_ctor_get(v_reader_896_, 5);
v_noMoreInput_902_ = lean_ctor_get_uint8(v_reader_896_, sizeof(void*)*6);
v_isSharedCheck_909_ = !lean_is_exclusive(v_reader_896_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; 
v_unused_910_ = lean_ctor_get(v_reader_896_, 1);
lean_dec(v_unused_910_);
v___x_904_ = v_reader_896_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_headerBytesRead_901_);
lean_inc(v_bodyBytesRead_900_);
lean_inc(v_messageCount_899_);
lean_inc(v_messageHead_898_);
lean_inc(v_state_897_);
lean_dec(v_reader_896_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_input_895_);
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_state_897_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_input_895_);
lean_ctor_set(v_reuseFailAlloc_908_, 2, v_messageHead_898_);
lean_ctor_set(v_reuseFailAlloc_908_, 3, v_messageCount_899_);
lean_ctor_set(v_reuseFailAlloc_908_, 4, v_bodyBytesRead_900_);
lean_ctor_set(v_reuseFailAlloc_908_, 5, v_headerBytesRead_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_908_, sizeof(void*)*6, v_noMoreInput_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_911_, lean_object* v_input_912_, lean_object* v_reader_913_){
_start:
{
lean_object* v_state_914_; lean_object* v_messageHead_915_; lean_object* v_messageCount_916_; lean_object* v_bodyBytesRead_917_; lean_object* v_headerBytesRead_918_; uint8_t v_noMoreInput_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_state_914_ = lean_ctor_get(v_reader_913_, 0);
v_messageHead_915_ = lean_ctor_get(v_reader_913_, 2);
v_messageCount_916_ = lean_ctor_get(v_reader_913_, 3);
v_bodyBytesRead_917_ = lean_ctor_get(v_reader_913_, 4);
v_headerBytesRead_918_ = lean_ctor_get(v_reader_913_, 5);
v_noMoreInput_919_ = lean_ctor_get_uint8(v_reader_913_, sizeof(void*)*6);
v_isSharedCheck_926_ = !lean_is_exclusive(v_reader_913_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_reader_913_, 1);
lean_dec(v_unused_927_);
v___x_921_ = v_reader_913_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_headerBytesRead_918_);
lean_inc(v_bodyBytesRead_917_);
lean_inc(v_messageCount_916_);
lean_inc(v_messageHead_915_);
lean_inc(v_state_914_);
lean_dec(v_reader_913_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v_input_912_);
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_state_914_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_input_912_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_messageHead_915_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_messageCount_916_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v_bodyBytesRead_917_);
lean_ctor_set(v_reuseFailAlloc_925_, 5, v_headerBytesRead_918_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*6, v_noMoreInput_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object* v_dir_928_, lean_object* v_input_929_, lean_object* v_reader_930_){
_start:
{
uint8_t v_dir_boxed_931_; lean_object* v_res_932_; 
v_dir_boxed_931_ = lean_unbox(v_dir_928_);
v_res_932_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_931_, v_input_929_, v_reader_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object* v_messageHead_933_, lean_object* v_reader_934_){
_start:
{
lean_object* v_state_935_; lean_object* v_input_936_; lean_object* v_messageCount_937_; lean_object* v_bodyBytesRead_938_; lean_object* v_headerBytesRead_939_; uint8_t v_noMoreInput_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_state_935_ = lean_ctor_get(v_reader_934_, 0);
v_input_936_ = lean_ctor_get(v_reader_934_, 1);
v_messageCount_937_ = lean_ctor_get(v_reader_934_, 3);
v_bodyBytesRead_938_ = lean_ctor_get(v_reader_934_, 4);
v_headerBytesRead_939_ = lean_ctor_get(v_reader_934_, 5);
v_noMoreInput_940_ = lean_ctor_get_uint8(v_reader_934_, sizeof(void*)*6);
v_isSharedCheck_947_ = !lean_is_exclusive(v_reader_934_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_reader_934_, 2);
lean_dec(v_unused_948_);
v___x_942_ = v_reader_934_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_headerBytesRead_939_);
lean_inc(v_bodyBytesRead_938_);
lean_inc(v_messageCount_937_);
lean_inc(v_input_936_);
lean_inc(v_state_935_);
lean_dec(v_reader_934_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v_messageHead_933_);
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_state_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_input_936_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_messageHead_933_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_messageCount_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_bodyBytesRead_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_headerBytesRead_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*6, v_noMoreInput_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_949_, lean_object* v_messageHead_950_, lean_object* v_reader_951_){
_start:
{
lean_object* v_state_952_; lean_object* v_input_953_; lean_object* v_messageCount_954_; lean_object* v_bodyBytesRead_955_; lean_object* v_headerBytesRead_956_; uint8_t v_noMoreInput_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
v_state_952_ = lean_ctor_get(v_reader_951_, 0);
v_input_953_ = lean_ctor_get(v_reader_951_, 1);
v_messageCount_954_ = lean_ctor_get(v_reader_951_, 3);
v_bodyBytesRead_955_ = lean_ctor_get(v_reader_951_, 4);
v_headerBytesRead_956_ = lean_ctor_get(v_reader_951_, 5);
v_noMoreInput_957_ = lean_ctor_get_uint8(v_reader_951_, sizeof(void*)*6);
v_isSharedCheck_964_ = !lean_is_exclusive(v_reader_951_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; 
v_unused_965_ = lean_ctor_get(v_reader_951_, 2);
lean_dec(v_unused_965_);
v___x_959_ = v_reader_951_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_headerBytesRead_956_);
lean_inc(v_bodyBytesRead_955_);
lean_inc(v_messageCount_954_);
lean_inc(v_input_953_);
lean_inc(v_state_952_);
lean_dec(v_reader_951_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 2, v_messageHead_950_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_state_952_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_input_953_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_messageHead_950_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_messageCount_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v_bodyBytesRead_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 5, v_headerBytesRead_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_963_, sizeof(void*)*6, v_noMoreInput_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_966_, lean_object* v_messageHead_967_, lean_object* v_reader_968_){
_start:
{
uint8_t v_dir_boxed_969_; lean_object* v_res_970_; 
v_dir_boxed_969_ = lean_unbox(v_dir_966_);
v_res_970_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_969_, v_messageHead_967_, v_reader_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(lean_object* v_i_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_972_) == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_975_ = lean_array_push(v___x_974_, v_i_971_);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
else
{
lean_object* v_val_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_985_; 
v_val_977_ = lean_ctor_get(v_x_972_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_985_ == 0)
{
v___x_979_ = v_x_972_;
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_val_977_);
lean_dec(v_x_972_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_array_push(v_val_977_, v_i_971_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_981_);
v___x_983_ = v___x_979_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_988_, lean_object* v_name_989_, lean_object* v_value_990_, lean_object* v_reader_991_){
_start:
{
if (v_dir_988_ == 0)
{
lean_object* v_messageHead_992_; lean_object* v_state_993_; lean_object* v_input_994_; lean_object* v_messageCount_995_; lean_object* v_bodyBytesRead_996_; lean_object* v_headerBytesRead_997_; uint8_t v_noMoreInput_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1034_; 
v_messageHead_992_ = lean_ctor_get(v_reader_991_, 2);
v_state_993_ = lean_ctor_get(v_reader_991_, 0);
v_input_994_ = lean_ctor_get(v_reader_991_, 1);
v_messageCount_995_ = lean_ctor_get(v_reader_991_, 3);
v_bodyBytesRead_996_ = lean_ctor_get(v_reader_991_, 4);
v_headerBytesRead_997_ = lean_ctor_get(v_reader_991_, 5);
v_noMoreInput_998_ = lean_ctor_get_uint8(v_reader_991_, sizeof(void*)*6);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_reader_991_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1000_ = v_reader_991_;
v_isShared_1001_ = v_isSharedCheck_1034_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_headerBytesRead_997_);
lean_inc(v_bodyBytesRead_996_);
lean_inc(v_messageCount_995_);
lean_inc(v_messageHead_992_);
lean_inc(v_input_994_);
lean_inc(v_state_993_);
lean_dec(v_reader_991_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1034_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
uint8_t v_method_1002_; uint8_t v_version_1003_; lean_object* v_uri_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1031_; 
v_method_1002_ = lean_ctor_get_uint8(v_messageHead_992_, sizeof(void*)*2);
v_version_1003_ = lean_ctor_get_uint8(v_messageHead_992_, sizeof(void*)*2 + 1);
v_uri_1004_ = lean_ctor_get(v_messageHead_992_, 0);
lean_inc(v_uri_1004_);
v___x_1005_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_988_, v_messageHead_992_);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_messageHead_992_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1032_ = lean_ctor_get(v_messageHead_992_, 1);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_messageHead_992_, 0);
lean_dec(v_unused_1033_);
v___x_1007_ = v_messageHead_992_;
v_isShared_1008_ = v_isSharedCheck_1031_;
goto v_resetjp_1006_;
}
else
{
lean_dec(v_messageHead_992_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1031_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_entries_1009_; lean_object* v_indexes_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1030_; 
v_entries_1009_ = lean_ctor_get(v___x_1005_, 0);
v_indexes_1010_ = lean_ctor_get(v___x_1005_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1012_ = v___x_1005_;
v_isShared_1013_ = v_isSharedCheck_1030_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_indexes_1010_);
lean_inc(v_entries_1009_);
lean_dec(v___x_1005_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1030_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v_i_1016_; lean_object* v_f_1017_; lean_object* v___x_1018_; lean_object* v_entries_1019_; lean_object* v_indexes_1020_; lean_object* v___x_1022_; 
v___f_1014_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1015_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1016_ = lean_array_get_size(v_entries_1009_);
v_f_1017_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1017_, 0, v_i_1016_);
lean_inc_ref(v_name_989_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_name_989_);
lean_ctor_set(v___x_1018_, 1, v_value_990_);
v_entries_1019_ = lean_array_push(v_entries_1009_, v___x_1018_);
v_indexes_1020_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1014_, v___f_1015_, v_indexes_1010_, v_name_989_, v_f_1017_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 1, v_indexes_1020_);
lean_ctor_set(v___x_1012_, 0, v_entries_1019_);
v___x_1022_ = v___x_1012_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_entries_1019_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_indexes_1020_);
v___x_1022_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1022_);
v___x_1024_ = v___x_1007_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_uri_1004_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*2, v_method_1002_);
lean_ctor_set_uint8(v_reuseFailAlloc_1028_, sizeof(void*)*2 + 1, v_version_1003_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 2, v___x_1024_);
v___x_1026_ = v___x_1000_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_state_993_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_input_994_);
lean_ctor_set(v_reuseFailAlloc_1027_, 2, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 3, v_messageCount_995_);
lean_ctor_set(v_reuseFailAlloc_1027_, 4, v_bodyBytesRead_996_);
lean_ctor_set(v_reuseFailAlloc_1027_, 5, v_headerBytesRead_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1027_, sizeof(void*)*6, v_noMoreInput_998_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
}
else
{
lean_object* v_messageHead_1035_; lean_object* v_state_1036_; lean_object* v_input_1037_; lean_object* v_messageCount_1038_; lean_object* v_bodyBytesRead_1039_; lean_object* v_headerBytesRead_1040_; uint8_t v_noMoreInput_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1076_; 
v_messageHead_1035_ = lean_ctor_get(v_reader_991_, 2);
v_state_1036_ = lean_ctor_get(v_reader_991_, 0);
v_input_1037_ = lean_ctor_get(v_reader_991_, 1);
v_messageCount_1038_ = lean_ctor_get(v_reader_991_, 3);
v_bodyBytesRead_1039_ = lean_ctor_get(v_reader_991_, 4);
v_headerBytesRead_1040_ = lean_ctor_get(v_reader_991_, 5);
v_noMoreInput_1041_ = lean_ctor_get_uint8(v_reader_991_, sizeof(void*)*6);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_reader_991_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1043_ = v_reader_991_;
v_isShared_1044_ = v_isSharedCheck_1076_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_headerBytesRead_1040_);
lean_inc(v_bodyBytesRead_1039_);
lean_inc(v_messageCount_1038_);
lean_inc(v_messageHead_1035_);
lean_inc(v_input_1037_);
lean_inc(v_state_1036_);
lean_dec(v_reader_991_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1076_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_status_1045_; uint8_t v_version_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1073_; 
v_status_1045_ = lean_ctor_get(v_messageHead_1035_, 0);
lean_inc(v_status_1045_);
v_version_1046_ = lean_ctor_get_uint8(v_messageHead_1035_, sizeof(void*)*2);
v___x_1047_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_988_, v_messageHead_1035_);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_messageHead_1035_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; lean_object* v_unused_1075_; 
v_unused_1074_ = lean_ctor_get(v_messageHead_1035_, 1);
lean_dec(v_unused_1074_);
v_unused_1075_ = lean_ctor_get(v_messageHead_1035_, 0);
lean_dec(v_unused_1075_);
v___x_1049_ = v_messageHead_1035_;
v_isShared_1050_ = v_isSharedCheck_1073_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v_messageHead_1035_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1073_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_entries_1051_; lean_object* v_indexes_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1072_; 
v_entries_1051_ = lean_ctor_get(v___x_1047_, 0);
v_indexes_1052_ = lean_ctor_get(v___x_1047_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1054_ = v___x_1047_;
v_isShared_1055_ = v_isSharedCheck_1072_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_indexes_1052_);
lean_inc(v_entries_1051_);
lean_dec(v___x_1047_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1072_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v_i_1058_; lean_object* v_f_1059_; lean_object* v___x_1060_; lean_object* v_entries_1061_; lean_object* v_indexes_1062_; lean_object* v___x_1064_; 
v___f_1056_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1057_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1058_ = lean_array_get_size(v_entries_1051_);
v_f_1059_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1059_, 0, v_i_1058_);
lean_inc_ref(v_name_989_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_name_989_);
lean_ctor_set(v___x_1060_, 1, v_value_990_);
v_entries_1061_ = lean_array_push(v_entries_1051_, v___x_1060_);
v_indexes_1062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1056_, v___f_1057_, v_indexes_1052_, v_name_989_, v_f_1059_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v_indexes_1062_);
lean_ctor_set(v___x_1054_, 0, v_entries_1061_);
v___x_1064_ = v___x_1054_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_entries_1061_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_indexes_1062_);
v___x_1064_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1064_);
v___x_1066_ = v___x_1049_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_status_1045_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1064_);
lean_ctor_set_uint8(v_reuseFailAlloc_1070_, sizeof(void*)*2, v_version_1046_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 2, v___x_1066_);
v___x_1068_ = v___x_1043_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_state_1036_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_input_1037_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_messageCount_1038_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_bodyBytesRead_1039_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_headerBytesRead_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*6, v_noMoreInput_1041_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1077_, lean_object* v_name_1078_, lean_object* v_value_1079_, lean_object* v_reader_1080_){
_start:
{
uint8_t v_dir_boxed_1081_; lean_object* v_res_1082_; 
v_dir_boxed_1081_ = lean_unbox(v_dir_1077_);
v_res_1082_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1081_, v_name_1078_, v_value_1079_, v_reader_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object* v_reader_1083_){
_start:
{
lean_object* v_input_1084_; lean_object* v_messageHead_1085_; lean_object* v_messageCount_1086_; lean_object* v_bodyBytesRead_1087_; lean_object* v_headerBytesRead_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1097_; 
v_input_1084_ = lean_ctor_get(v_reader_1083_, 1);
v_messageHead_1085_ = lean_ctor_get(v_reader_1083_, 2);
v_messageCount_1086_ = lean_ctor_get(v_reader_1083_, 3);
v_bodyBytesRead_1087_ = lean_ctor_get(v_reader_1083_, 4);
v_headerBytesRead_1088_ = lean_ctor_get(v_reader_1083_, 5);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_reader_1083_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; 
v_unused_1098_ = lean_ctor_get(v_reader_1083_, 0);
lean_dec(v_unused_1098_);
v___x_1090_ = v_reader_1083_;
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_headerBytesRead_1088_);
lean_inc(v_bodyBytesRead_1087_);
lean_inc(v_messageCount_1086_);
lean_inc(v_messageHead_1085_);
lean_inc(v_input_1084_);
lean_dec(v_reader_1083_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1097_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1095_; 
v___x_1092_ = lean_box(6);
v___x_1093_ = 1;
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_input_1084_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_messageHead_1085_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_messageCount_1086_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_bodyBytesRead_1087_);
lean_ctor_set(v_reuseFailAlloc_1096_, 5, v_headerBytesRead_1088_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*6, v___x_1093_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t v_dir_1099_, lean_object* v_reader_1100_){
_start:
{
lean_object* v_input_1101_; lean_object* v_messageHead_1102_; lean_object* v_messageCount_1103_; lean_object* v_bodyBytesRead_1104_; lean_object* v_headerBytesRead_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
v_input_1101_ = lean_ctor_get(v_reader_1100_, 1);
v_messageHead_1102_ = lean_ctor_get(v_reader_1100_, 2);
v_messageCount_1103_ = lean_ctor_get(v_reader_1100_, 3);
v_bodyBytesRead_1104_ = lean_ctor_get(v_reader_1100_, 4);
v_headerBytesRead_1105_ = lean_ctor_get(v_reader_1100_, 5);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_reader_1100_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; 
v_unused_1115_ = lean_ctor_get(v_reader_1100_, 0);
lean_dec(v_unused_1115_);
v___x_1107_ = v_reader_1100_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_headerBytesRead_1105_);
lean_inc(v_bodyBytesRead_1104_);
lean_inc(v_messageCount_1103_);
lean_inc(v_messageHead_1102_);
lean_inc(v_input_1101_);
lean_dec(v_reader_1100_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = lean_box(6);
v___x_1110_ = 1;
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_input_1101_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_messageHead_1102_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_messageCount_1103_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_bodyBytesRead_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v_headerBytesRead_1105_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*6, v___x_1110_);
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object* v_dir_1116_, lean_object* v_reader_1117_){
_start:
{
uint8_t v_dir_boxed_1118_; lean_object* v_res_1119_; 
v_dir_boxed_1118_ = lean_unbox(v_dir_1116_);
v_res_1119_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_1118_, v_reader_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1120_){
_start:
{
lean_object* v_input_1121_; lean_object* v_messageHead_1122_; lean_object* v_messageCount_1123_; lean_object* v_bodyBytesRead_1124_; lean_object* v_headerBytesRead_1125_; uint8_t v_noMoreInput_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1136_; 
v_input_1121_ = lean_ctor_get(v_reader_1120_, 1);
v_messageHead_1122_ = lean_ctor_get(v_reader_1120_, 2);
v_messageCount_1123_ = lean_ctor_get(v_reader_1120_, 3);
v_bodyBytesRead_1124_ = lean_ctor_get(v_reader_1120_, 4);
v_headerBytesRead_1125_ = lean_ctor_get(v_reader_1120_, 5);
v_noMoreInput_1126_ = lean_ctor_get_uint8(v_reader_1120_, sizeof(void*)*6);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_reader_1120_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_reader_1120_, 0);
lean_dec(v_unused_1137_);
v___x_1128_ = v_reader_1120_;
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_headerBytesRead_1125_);
lean_inc(v_bodyBytesRead_1124_);
lean_inc(v_messageCount_1123_);
lean_inc(v_messageHead_1122_);
lean_inc(v_input_1121_);
lean_dec(v_reader_1120_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1130_ = lean_box(5);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_messageCount_1123_, v___x_1131_);
lean_dec(v_messageCount_1123_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 3, v___x_1132_);
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1134_ = v___x_1128_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_input_1121_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_messageHead_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_bodyBytesRead_1124_);
lean_ctor_set(v_reuseFailAlloc_1135_, 5, v_headerBytesRead_1125_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*6, v_noMoreInput_1126_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1138_, lean_object* v_reader_1139_){
_start:
{
lean_object* v_input_1140_; lean_object* v_messageHead_1141_; lean_object* v_messageCount_1142_; lean_object* v_bodyBytesRead_1143_; lean_object* v_headerBytesRead_1144_; uint8_t v_noMoreInput_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v_input_1140_ = lean_ctor_get(v_reader_1139_, 1);
v_messageHead_1141_ = lean_ctor_get(v_reader_1139_, 2);
v_messageCount_1142_ = lean_ctor_get(v_reader_1139_, 3);
v_bodyBytesRead_1143_ = lean_ctor_get(v_reader_1139_, 4);
v_headerBytesRead_1144_ = lean_ctor_get(v_reader_1139_, 5);
v_noMoreInput_1145_ = lean_ctor_get_uint8(v_reader_1139_, sizeof(void*)*6);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_reader_1139_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v_reader_1139_, 0);
lean_dec(v_unused_1156_);
v___x_1147_ = v_reader_1139_;
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_headerBytesRead_1144_);
lean_inc(v_bodyBytesRead_1143_);
lean_inc(v_messageCount_1142_);
lean_inc(v_messageHead_1141_);
lean_inc(v_input_1140_);
lean_dec(v_reader_1139_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1149_ = lean_box(5);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_messageCount_1142_, v___x_1150_);
lean_dec(v_messageCount_1142_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 3, v___x_1151_);
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1153_ = v___x_1147_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_input_1140_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_messageHead_1141_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_bodyBytesRead_1143_);
lean_ctor_set(v_reuseFailAlloc_1154_, 5, v_headerBytesRead_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*6, v_noMoreInput_1145_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object* v_dir_1157_, lean_object* v_reader_1158_){
_start:
{
uint8_t v_dir_boxed_1159_; lean_object* v_res_1160_; 
v_dir_boxed_1159_ = lean_unbox(v_dir_1157_);
v_res_1160_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_1159_, v_reader_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object* v_error_1161_, lean_object* v_reader_1162_){
_start:
{
lean_object* v_input_1163_; lean_object* v_messageHead_1164_; lean_object* v_messageCount_1165_; lean_object* v_bodyBytesRead_1166_; lean_object* v_headerBytesRead_1167_; uint8_t v_noMoreInput_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1176_; 
v_input_1163_ = lean_ctor_get(v_reader_1162_, 1);
v_messageHead_1164_ = lean_ctor_get(v_reader_1162_, 2);
v_messageCount_1165_ = lean_ctor_get(v_reader_1162_, 3);
v_bodyBytesRead_1166_ = lean_ctor_get(v_reader_1162_, 4);
v_headerBytesRead_1167_ = lean_ctor_get(v_reader_1162_, 5);
v_noMoreInput_1168_ = lean_ctor_get_uint8(v_reader_1162_, sizeof(void*)*6);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_reader_1162_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v_reader_1162_, 0);
lean_dec(v_unused_1177_);
v___x_1170_ = v_reader_1162_;
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_headerBytesRead_1167_);
lean_inc(v_bodyBytesRead_1166_);
lean_inc(v_messageCount_1165_);
lean_inc(v_messageHead_1164_);
lean_inc(v_input_1163_);
lean_dec(v_reader_1162_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1176_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_error_1161_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1174_ = v___x_1170_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_input_1163_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_messageHead_1164_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_messageCount_1165_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_bodyBytesRead_1166_);
lean_ctor_set(v_reuseFailAlloc_1175_, 5, v_headerBytesRead_1167_);
lean_ctor_set_uint8(v_reuseFailAlloc_1175_, sizeof(void*)*6, v_noMoreInput_1168_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t v_dir_1178_, lean_object* v_error_1179_, lean_object* v_reader_1180_){
_start:
{
lean_object* v_input_1181_; lean_object* v_messageHead_1182_; lean_object* v_messageCount_1183_; lean_object* v_bodyBytesRead_1184_; lean_object* v_headerBytesRead_1185_; uint8_t v_noMoreInput_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
v_input_1181_ = lean_ctor_get(v_reader_1180_, 1);
v_messageHead_1182_ = lean_ctor_get(v_reader_1180_, 2);
v_messageCount_1183_ = lean_ctor_get(v_reader_1180_, 3);
v_bodyBytesRead_1184_ = lean_ctor_get(v_reader_1180_, 4);
v_headerBytesRead_1185_ = lean_ctor_get(v_reader_1180_, 5);
v_noMoreInput_1186_ = lean_ctor_get_uint8(v_reader_1180_, sizeof(void*)*6);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_reader_1180_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_reader_1180_, 0);
lean_dec(v_unused_1195_);
v___x_1188_ = v_reader_1180_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_headerBytesRead_1185_);
lean_inc(v_bodyBytesRead_1184_);
lean_inc(v_messageCount_1183_);
lean_inc(v_messageHead_1182_);
lean_inc(v_input_1181_);
lean_dec(v_reader_1180_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1190_, 0, v_error_1179_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_input_1181_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_messageHead_1182_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_messageCount_1183_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_bodyBytesRead_1184_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_headerBytesRead_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*6, v_noMoreInput_1186_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object* v_dir_1196_, lean_object* v_error_1197_, lean_object* v_reader_1198_){
_start:
{
uint8_t v_dir_boxed_1199_; lean_object* v_res_1200_; 
v_dir_boxed_1199_ = lean_unbox(v_dir_1196_);
v_res_1200_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_1199_, v_error_1197_, v_reader_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1201_, lean_object* v_reader_1202_){
_start:
{
lean_object* v_input_1203_; lean_object* v_messageCount_1204_; uint8_t v_noMoreInput_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1215_; 
v_input_1203_ = lean_ctor_get(v_reader_1202_, 1);
v_messageCount_1204_ = lean_ctor_get(v_reader_1202_, 3);
v_noMoreInput_1205_ = lean_ctor_get_uint8(v_reader_1202_, sizeof(void*)*6);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_reader_1202_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; lean_object* v_unused_1217_; lean_object* v_unused_1218_; lean_object* v_unused_1219_; 
v_unused_1216_ = lean_ctor_get(v_reader_1202_, 5);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_reader_1202_, 4);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_reader_1202_, 2);
lean_dec(v_unused_1218_);
v_unused_1219_ = lean_ctor_get(v_reader_1202_, 0);
lean_dec(v_unused_1219_);
v___x_1207_ = v_reader_1202_;
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_messageCount_1204_);
lean_inc(v_input_1203_);
lean_dec(v_reader_1202_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1215_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1201_);
v___x_1211_ = lean_unsigned_to_nat(0u);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 5, v___x_1211_);
lean_ctor_set(v___x_1207_, 4, v___x_1211_);
lean_ctor_set(v___x_1207_, 2, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1213_ = v___x_1207_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_input_1203_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_messageCount_1204_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1214_, 5, v___x_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*6, v_noMoreInput_1205_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1220_, lean_object* v_reader_1221_){
_start:
{
uint8_t v_dir_boxed_1222_; lean_object* v_res_1223_; 
v_dir_boxed_1222_ = lean_unbox(v_dir_1220_);
v_res_1223_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1222_, v_reader_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1224_){
_start:
{
lean_object* v_input_1225_; lean_object* v_state_1226_; uint8_t v_noMoreInput_1227_; lean_object* v_array_1228_; lean_object* v_idx_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_input_1225_ = lean_ctor_get(v_reader_1224_, 1);
v_state_1226_ = lean_ctor_get(v_reader_1224_, 0);
v_noMoreInput_1227_ = lean_ctor_get_uint8(v_reader_1224_, sizeof(void*)*6);
v_array_1228_ = lean_ctor_get(v_input_1225_, 0);
v_idx_1229_ = lean_ctor_get(v_input_1225_, 1);
v___x_1230_ = lean_byte_array_size(v_array_1228_);
v___x_1231_ = lean_nat_dec_le(v___x_1230_, v_idx_1229_);
if (v___x_1231_ == 0)
{
return v___x_1231_;
}
else
{
if (v_noMoreInput_1227_ == 0)
{
switch(lean_obj_tag(v_state_1226_))
{
case 5:
{
return v_noMoreInput_1227_;
}
case 6:
{
return v_noMoreInput_1227_;
}
case 7:
{
return v_noMoreInput_1227_;
}
case 3:
{
return v_noMoreInput_1227_;
}
default: 
{
return v___x_1231_;
}
}
}
else
{
uint8_t v___x_1232_; 
v___x_1232_ = 0;
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1233_);
lean_dec_ref(v_reader_1233_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1236_, lean_object* v_reader_1237_){
_start:
{
lean_object* v_input_1238_; lean_object* v_state_1239_; uint8_t v_noMoreInput_1240_; lean_object* v_array_1241_; lean_object* v_idx_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_input_1238_ = lean_ctor_get(v_reader_1237_, 1);
v_state_1239_ = lean_ctor_get(v_reader_1237_, 0);
v_noMoreInput_1240_ = lean_ctor_get_uint8(v_reader_1237_, sizeof(void*)*6);
v_array_1241_ = lean_ctor_get(v_input_1238_, 0);
v_idx_1242_ = lean_ctor_get(v_input_1238_, 1);
v___x_1243_ = lean_byte_array_size(v_array_1241_);
v___x_1244_ = lean_nat_dec_le(v___x_1243_, v_idx_1242_);
if (v___x_1244_ == 0)
{
return v___x_1244_;
}
else
{
if (v_noMoreInput_1240_ == 0)
{
switch(lean_obj_tag(v_state_1239_))
{
case 5:
{
return v_noMoreInput_1240_;
}
case 6:
{
return v_noMoreInput_1240_;
}
case 7:
{
return v_noMoreInput_1240_;
}
case 3:
{
return v_noMoreInput_1240_;
}
default: 
{
return v___x_1244_;
}
}
}
else
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1246_, lean_object* v_reader_1247_){
_start:
{
uint8_t v_dir_boxed_1248_; uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_dir_boxed_1248_ = lean_unbox(v_dir_1246_);
v_res_1249_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1248_, v_reader_1247_);
lean_dec_ref(v_reader_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object* v_reader_1251_){
_start:
{
lean_object* v_state_1252_; 
v_state_1252_ = lean_ctor_get(v_reader_1251_, 0);
lean_inc(v_state_1252_);
lean_dec_ref(v_reader_1251_);
if (lean_obj_tag(v_state_1252_) == 7)
{
lean_object* v_error_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_error_1253_ = lean_ctor_get(v_state_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_state_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v_state_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_error_1253_);
lean_dec(v_state_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_error_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_state_1252_);
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t v_dir_1262_, lean_object* v_reader_1263_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object* v_dir_1274_, lean_object* v_reader_1275_){
_start:
{
uint8_t v_dir_boxed_1276_; lean_object* v_res_1277_; 
v_dir_boxed_1276_ = lean_unbox(v_dir_1274_);
v_res_1277_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_1276_, v_reader_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1278_){
_start:
{
lean_object* v_input_1279_; lean_object* v_array_1280_; lean_object* v_idx_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_input_1279_ = lean_ctor_get(v_reader_1278_, 1);
v_array_1280_ = lean_ctor_get(v_input_1279_, 0);
v_idx_1281_ = lean_ctor_get(v_input_1279_, 1);
v___x_1282_ = lean_byte_array_size(v_array_1280_);
v___x_1283_ = lean_nat_sub(v___x_1282_, v_idx_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1284_);
lean_dec_ref(v_reader_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1286_, lean_object* v_reader_1287_){
_start:
{
lean_object* v_input_1288_; lean_object* v_array_1289_; lean_object* v_idx_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_input_1288_ = lean_ctor_get(v_reader_1287_, 1);
v_array_1289_ = lean_ctor_get(v_input_1288_, 0);
v_idx_1290_ = lean_ctor_get(v_input_1288_, 1);
v___x_1291_ = lean_byte_array_size(v_array_1289_);
v___x_1292_ = lean_nat_sub(v___x_1291_, v_idx_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1293_, lean_object* v_reader_1294_){
_start:
{
uint8_t v_dir_boxed_1295_; lean_object* v_res_1296_; 
v_dir_boxed_1295_ = lean_unbox(v_dir_1293_);
v_res_1296_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1295_, v_reader_1294_);
lean_dec_ref(v_reader_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1297_, lean_object* v_reader_1298_){
_start:
{
lean_object* v_input_1299_; lean_object* v_state_1300_; lean_object* v_messageHead_1301_; lean_object* v_messageCount_1302_; lean_object* v_bodyBytesRead_1303_; lean_object* v_headerBytesRead_1304_; uint8_t v_noMoreInput_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1322_; 
v_input_1299_ = lean_ctor_get(v_reader_1298_, 1);
v_state_1300_ = lean_ctor_get(v_reader_1298_, 0);
v_messageHead_1301_ = lean_ctor_get(v_reader_1298_, 2);
v_messageCount_1302_ = lean_ctor_get(v_reader_1298_, 3);
v_bodyBytesRead_1303_ = lean_ctor_get(v_reader_1298_, 4);
v_headerBytesRead_1304_ = lean_ctor_get(v_reader_1298_, 5);
v_noMoreInput_1305_ = lean_ctor_get_uint8(v_reader_1298_, sizeof(void*)*6);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_reader_1298_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1307_ = v_reader_1298_;
v_isShared_1308_ = v_isSharedCheck_1322_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_headerBytesRead_1304_);
lean_inc(v_bodyBytesRead_1303_);
lean_inc(v_messageCount_1302_);
lean_inc(v_messageHead_1301_);
lean_inc(v_input_1299_);
lean_inc(v_state_1300_);
lean_dec(v_reader_1298_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1322_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_array_1309_; lean_object* v_idx_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1321_; 
v_array_1309_ = lean_ctor_get(v_input_1299_, 0);
v_idx_1310_ = lean_ctor_get(v_input_1299_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_input_1299_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1312_ = v_input_1299_;
v_isShared_1313_ = v_isSharedCheck_1321_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_idx_1310_);
lean_inc(v_array_1309_);
lean_dec(v_input_1299_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1321_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_nat_add(v_idx_1310_, v_n_1297_);
lean_dec(v_idx_1310_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_array_1309_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___x_1316_);
v___x_1318_ = v___x_1307_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_state_1300_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_messageHead_1301_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_messageCount_1302_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_bodyBytesRead_1303_);
lean_ctor_set(v_reuseFailAlloc_1319_, 5, v_headerBytesRead_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*6, v_noMoreInput_1305_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1323_, lean_object* v_reader_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1323_, v_reader_1324_);
lean_dec(v_n_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1326_, lean_object* v_n_1327_, lean_object* v_reader_1328_){
_start:
{
lean_object* v_input_1329_; lean_object* v_state_1330_; lean_object* v_messageHead_1331_; lean_object* v_messageCount_1332_; lean_object* v_bodyBytesRead_1333_; lean_object* v_headerBytesRead_1334_; uint8_t v_noMoreInput_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1352_; 
v_input_1329_ = lean_ctor_get(v_reader_1328_, 1);
v_state_1330_ = lean_ctor_get(v_reader_1328_, 0);
v_messageHead_1331_ = lean_ctor_get(v_reader_1328_, 2);
v_messageCount_1332_ = lean_ctor_get(v_reader_1328_, 3);
v_bodyBytesRead_1333_ = lean_ctor_get(v_reader_1328_, 4);
v_headerBytesRead_1334_ = lean_ctor_get(v_reader_1328_, 5);
v_noMoreInput_1335_ = lean_ctor_get_uint8(v_reader_1328_, sizeof(void*)*6);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_reader_1328_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1337_ = v_reader_1328_;
v_isShared_1338_ = v_isSharedCheck_1352_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_headerBytesRead_1334_);
lean_inc(v_bodyBytesRead_1333_);
lean_inc(v_messageCount_1332_);
lean_inc(v_messageHead_1331_);
lean_inc(v_input_1329_);
lean_inc(v_state_1330_);
lean_dec(v_reader_1328_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1352_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_array_1339_; lean_object* v_idx_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1351_; 
v_array_1339_ = lean_ctor_get(v_input_1329_, 0);
v_idx_1340_ = lean_ctor_get(v_input_1329_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_input_1329_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1342_ = v_input_1329_;
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_idx_1340_);
lean_inc(v_array_1339_);
lean_dec(v_input_1329_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1351_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = lean_nat_add(v_idx_1340_, v_n_1327_);
lean_dec(v_idx_1340_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v___x_1344_);
v___x_1346_ = v___x_1342_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_array_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v___x_1346_);
v___x_1348_ = v___x_1337_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_state_1330_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_messageHead_1331_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_messageCount_1332_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_bodyBytesRead_1333_);
lean_ctor_set(v_reuseFailAlloc_1349_, 5, v_headerBytesRead_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1349_, sizeof(void*)*6, v_noMoreInput_1335_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1353_, lean_object* v_n_1354_, lean_object* v_reader_1355_){
_start:
{
uint8_t v_dir_boxed_1356_; lean_object* v_res_1357_; 
v_dir_boxed_1356_ = lean_unbox(v_dir_1353_);
v_res_1357_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1356_, v_n_1354_, v_reader_1355_);
lean_dec(v_n_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1360_){
_start:
{
lean_object* v_input_1361_; lean_object* v_messageHead_1362_; lean_object* v_messageCount_1363_; uint8_t v_noMoreInput_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1373_; 
v_input_1361_ = lean_ctor_get(v_reader_1360_, 1);
v_messageHead_1362_ = lean_ctor_get(v_reader_1360_, 2);
v_messageCount_1363_ = lean_ctor_get(v_reader_1360_, 3);
v_noMoreInput_1364_ = lean_ctor_get_uint8(v_reader_1360_, sizeof(void*)*6);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_reader_1360_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1374_ = lean_ctor_get(v_reader_1360_, 5);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_reader_1360_, 4);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_reader_1360_, 0);
lean_dec(v_unused_1376_);
v___x_1366_ = v_reader_1360_;
v_isShared_1367_ = v_isSharedCheck_1373_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_messageCount_1363_);
lean_inc(v_messageHead_1362_);
lean_inc(v_input_1361_);
lean_dec(v_reader_1360_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1373_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 5, v___x_1368_);
lean_ctor_set(v___x_1366_, 4, v___x_1368_);
lean_ctor_set(v___x_1366_, 0, v___x_1369_);
v___x_1371_ = v___x_1366_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_input_1361_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_messageHead_1362_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_messageCount_1363_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1372_, 5, v___x_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1372_, sizeof(void*)*6, v_noMoreInput_1364_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1377_, lean_object* v_reader_1378_){
_start:
{
lean_object* v_input_1379_; lean_object* v_messageHead_1380_; lean_object* v_messageCount_1381_; uint8_t v_noMoreInput_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
v_input_1379_ = lean_ctor_get(v_reader_1378_, 1);
v_messageHead_1380_ = lean_ctor_get(v_reader_1378_, 2);
v_messageCount_1381_ = lean_ctor_get(v_reader_1378_, 3);
v_noMoreInput_1382_ = lean_ctor_get_uint8(v_reader_1378_, sizeof(void*)*6);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_reader_1378_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; lean_object* v_unused_1393_; lean_object* v_unused_1394_; 
v_unused_1392_ = lean_ctor_get(v_reader_1378_, 5);
lean_dec(v_unused_1392_);
v_unused_1393_ = lean_ctor_get(v_reader_1378_, 4);
lean_dec(v_unused_1393_);
v_unused_1394_ = lean_ctor_get(v_reader_1378_, 0);
lean_dec(v_unused_1394_);
v___x_1384_ = v_reader_1378_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_messageCount_1381_);
lean_inc(v_messageHead_1380_);
lean_inc(v_input_1379_);
lean_dec(v_reader_1378_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 5, v___x_1386_);
lean_ctor_set(v___x_1384_, 4, v___x_1386_);
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_input_1379_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_messageHead_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_messageCount_1381_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v___x_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*6, v_noMoreInput_1382_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1395_, lean_object* v_reader_1396_){
_start:
{
uint8_t v_dir_boxed_1397_; lean_object* v_res_1398_; 
v_dir_boxed_1397_ = lean_unbox(v_dir_1395_);
v_res_1398_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1397_, v_reader_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1399_, lean_object* v_reader_1400_){
_start:
{
lean_object* v_state_1401_; lean_object* v_input_1402_; lean_object* v_messageHead_1403_; lean_object* v_messageCount_1404_; lean_object* v_bodyBytesRead_1405_; lean_object* v_headerBytesRead_1406_; uint8_t v_noMoreInput_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_state_1401_ = lean_ctor_get(v_reader_1400_, 0);
v_input_1402_ = lean_ctor_get(v_reader_1400_, 1);
v_messageHead_1403_ = lean_ctor_get(v_reader_1400_, 2);
v_messageCount_1404_ = lean_ctor_get(v_reader_1400_, 3);
v_bodyBytesRead_1405_ = lean_ctor_get(v_reader_1400_, 4);
v_headerBytesRead_1406_ = lean_ctor_get(v_reader_1400_, 5);
v_noMoreInput_1407_ = lean_ctor_get_uint8(v_reader_1400_, sizeof(void*)*6);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_reader_1400_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v_reader_1400_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_headerBytesRead_1406_);
lean_inc(v_bodyBytesRead_1405_);
lean_inc(v_messageCount_1404_);
lean_inc(v_messageHead_1403_);
lean_inc(v_input_1402_);
lean_inc(v_state_1401_);
lean_dec(v_reader_1400_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_nat_add(v_bodyBytesRead_1405_, v_n_1399_);
lean_dec(v_bodyBytesRead_1405_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_state_1401_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_input_1402_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_messageHead_1403_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_messageCount_1404_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1414_, 5, v_headerBytesRead_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1414_, sizeof(void*)*6, v_noMoreInput_1407_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1416_, lean_object* v_reader_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1416_, v_reader_1417_);
lean_dec(v_n_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1419_, lean_object* v_n_1420_, lean_object* v_reader_1421_){
_start:
{
lean_object* v_state_1422_; lean_object* v_input_1423_; lean_object* v_messageHead_1424_; lean_object* v_messageCount_1425_; lean_object* v_bodyBytesRead_1426_; lean_object* v_headerBytesRead_1427_; uint8_t v_noMoreInput_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1436_; 
v_state_1422_ = lean_ctor_get(v_reader_1421_, 0);
v_input_1423_ = lean_ctor_get(v_reader_1421_, 1);
v_messageHead_1424_ = lean_ctor_get(v_reader_1421_, 2);
v_messageCount_1425_ = lean_ctor_get(v_reader_1421_, 3);
v_bodyBytesRead_1426_ = lean_ctor_get(v_reader_1421_, 4);
v_headerBytesRead_1427_ = lean_ctor_get(v_reader_1421_, 5);
v_noMoreInput_1428_ = lean_ctor_get_uint8(v_reader_1421_, sizeof(void*)*6);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_reader_1421_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1430_ = v_reader_1421_;
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_headerBytesRead_1427_);
lean_inc(v_bodyBytesRead_1426_);
lean_inc(v_messageCount_1425_);
lean_inc(v_messageHead_1424_);
lean_inc(v_input_1423_);
lean_inc(v_state_1422_);
lean_dec(v_reader_1421_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1436_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_nat_add(v_bodyBytesRead_1426_, v_n_1420_);
lean_dec(v_bodyBytesRead_1426_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_state_1422_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_input_1423_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_messageHead_1424_);
lean_ctor_set(v_reuseFailAlloc_1435_, 3, v_messageCount_1425_);
lean_ctor_set(v_reuseFailAlloc_1435_, 4, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1435_, 5, v_headerBytesRead_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1435_, sizeof(void*)*6, v_noMoreInput_1428_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1437_, lean_object* v_n_1438_, lean_object* v_reader_1439_){
_start:
{
uint8_t v_dir_boxed_1440_; lean_object* v_res_1441_; 
v_dir_boxed_1440_ = lean_unbox(v_dir_1437_);
v_res_1441_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1440_, v_n_1438_, v_reader_1439_);
lean_dec(v_n_1438_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1442_, lean_object* v_reader_1443_){
_start:
{
lean_object* v_state_1444_; lean_object* v_input_1445_; lean_object* v_messageHead_1446_; lean_object* v_messageCount_1447_; lean_object* v_bodyBytesRead_1448_; lean_object* v_headerBytesRead_1449_; uint8_t v_noMoreInput_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_state_1444_ = lean_ctor_get(v_reader_1443_, 0);
v_input_1445_ = lean_ctor_get(v_reader_1443_, 1);
v_messageHead_1446_ = lean_ctor_get(v_reader_1443_, 2);
v_messageCount_1447_ = lean_ctor_get(v_reader_1443_, 3);
v_bodyBytesRead_1448_ = lean_ctor_get(v_reader_1443_, 4);
v_headerBytesRead_1449_ = lean_ctor_get(v_reader_1443_, 5);
v_noMoreInput_1450_ = lean_ctor_get_uint8(v_reader_1443_, sizeof(void*)*6);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_reader_1443_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v_reader_1443_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_headerBytesRead_1449_);
lean_inc(v_bodyBytesRead_1448_);
lean_inc(v_messageCount_1447_);
lean_inc(v_messageHead_1446_);
lean_inc(v_input_1445_);
lean_inc(v_state_1444_);
lean_dec(v_reader_1443_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_nat_add(v_headerBytesRead_1449_, v_n_1442_);
lean_dec(v_headerBytesRead_1449_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 5, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_state_1444_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_input_1445_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_messageHead_1446_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_messageCount_1447_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_bodyBytesRead_1448_);
lean_ctor_set(v_reuseFailAlloc_1457_, 5, v___x_1454_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*6, v_noMoreInput_1450_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1459_, lean_object* v_reader_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1459_, v_reader_1460_);
lean_dec(v_n_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1462_, lean_object* v_n_1463_, lean_object* v_reader_1464_){
_start:
{
lean_object* v_state_1465_; lean_object* v_input_1466_; lean_object* v_messageHead_1467_; lean_object* v_messageCount_1468_; lean_object* v_bodyBytesRead_1469_; lean_object* v_headerBytesRead_1470_; uint8_t v_noMoreInput_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1479_; 
v_state_1465_ = lean_ctor_get(v_reader_1464_, 0);
v_input_1466_ = lean_ctor_get(v_reader_1464_, 1);
v_messageHead_1467_ = lean_ctor_get(v_reader_1464_, 2);
v_messageCount_1468_ = lean_ctor_get(v_reader_1464_, 3);
v_bodyBytesRead_1469_ = lean_ctor_get(v_reader_1464_, 4);
v_headerBytesRead_1470_ = lean_ctor_get(v_reader_1464_, 5);
v_noMoreInput_1471_ = lean_ctor_get_uint8(v_reader_1464_, sizeof(void*)*6);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_reader_1464_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1473_ = v_reader_1464_;
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_headerBytesRead_1470_);
lean_inc(v_bodyBytesRead_1469_);
lean_inc(v_messageCount_1468_);
lean_inc(v_messageHead_1467_);
lean_inc(v_input_1466_);
lean_inc(v_state_1465_);
lean_dec(v_reader_1464_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1479_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_nat_add(v_headerBytesRead_1470_, v_n_1463_);
lean_dec(v_headerBytesRead_1470_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 5, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_state_1465_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_input_1466_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_messageHead_1467_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_messageCount_1468_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_bodyBytesRead_1469_);
lean_ctor_set(v_reuseFailAlloc_1478_, 5, v___x_1475_);
lean_ctor_set_uint8(v_reuseFailAlloc_1478_, sizeof(void*)*6, v_noMoreInput_1471_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1480_, lean_object* v_n_1481_, lean_object* v_reader_1482_){
_start:
{
uint8_t v_dir_boxed_1483_; lean_object* v_res_1484_; 
v_dir_boxed_1483_ = lean_unbox(v_dir_1480_);
v_res_1484_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1483_, v_n_1481_, v_reader_1482_);
lean_dec(v_n_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1485_, lean_object* v_reader_1486_){
_start:
{
lean_object* v_input_1487_; lean_object* v_messageHead_1488_; lean_object* v_messageCount_1489_; lean_object* v_bodyBytesRead_1490_; lean_object* v_headerBytesRead_1491_; uint8_t v_noMoreInput_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1501_; 
v_input_1487_ = lean_ctor_get(v_reader_1486_, 1);
v_messageHead_1488_ = lean_ctor_get(v_reader_1486_, 2);
v_messageCount_1489_ = lean_ctor_get(v_reader_1486_, 3);
v_bodyBytesRead_1490_ = lean_ctor_get(v_reader_1486_, 4);
v_headerBytesRead_1491_ = lean_ctor_get(v_reader_1486_, 5);
v_noMoreInput_1492_ = lean_ctor_get_uint8(v_reader_1486_, sizeof(void*)*6);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_reader_1486_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_reader_1486_, 0);
lean_dec(v_unused_1502_);
v___x_1494_ = v_reader_1486_;
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_headerBytesRead_1491_);
lean_inc(v_bodyBytesRead_1490_);
lean_inc(v_messageCount_1489_);
lean_inc(v_messageHead_1488_);
lean_inc(v_input_1487_);
lean_dec(v_reader_1486_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1501_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_size_1485_);
v___x_1497_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 0, v___x_1497_);
v___x_1499_ = v___x_1494_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_input_1487_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_messageHead_1488_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_messageCount_1489_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_bodyBytesRead_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 5, v_headerBytesRead_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1500_, sizeof(void*)*6, v_noMoreInput_1492_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1503_, lean_object* v_size_1504_, lean_object* v_reader_1505_){
_start:
{
lean_object* v_input_1506_; lean_object* v_messageHead_1507_; lean_object* v_messageCount_1508_; lean_object* v_bodyBytesRead_1509_; lean_object* v_headerBytesRead_1510_; uint8_t v_noMoreInput_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1520_; 
v_input_1506_ = lean_ctor_get(v_reader_1505_, 1);
v_messageHead_1507_ = lean_ctor_get(v_reader_1505_, 2);
v_messageCount_1508_ = lean_ctor_get(v_reader_1505_, 3);
v_bodyBytesRead_1509_ = lean_ctor_get(v_reader_1505_, 4);
v_headerBytesRead_1510_ = lean_ctor_get(v_reader_1505_, 5);
v_noMoreInput_1511_ = lean_ctor_get_uint8(v_reader_1505_, sizeof(void*)*6);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_reader_1505_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v_reader_1505_, 0);
lean_dec(v_unused_1521_);
v___x_1513_ = v_reader_1505_;
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_headerBytesRead_1510_);
lean_inc(v_bodyBytesRead_1509_);
lean_inc(v_messageCount_1508_);
lean_inc(v_messageHead_1507_);
lean_inc(v_input_1506_);
lean_dec(v_reader_1505_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1520_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_size_1504_);
v___x_1516_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1516_);
v___x_1518_ = v___x_1513_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_input_1506_);
lean_ctor_set(v_reuseFailAlloc_1519_, 2, v_messageHead_1507_);
lean_ctor_set(v_reuseFailAlloc_1519_, 3, v_messageCount_1508_);
lean_ctor_set(v_reuseFailAlloc_1519_, 4, v_bodyBytesRead_1509_);
lean_ctor_set(v_reuseFailAlloc_1519_, 5, v_headerBytesRead_1510_);
lean_ctor_set_uint8(v_reuseFailAlloc_1519_, sizeof(void*)*6, v_noMoreInput_1511_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1522_, lean_object* v_size_1523_, lean_object* v_reader_1524_){
_start:
{
uint8_t v_dir_boxed_1525_; lean_object* v_res_1526_; 
v_dir_boxed_1525_ = lean_unbox(v_dir_1522_);
v_res_1526_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1525_, v_size_1523_, v_reader_1524_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1529_){
_start:
{
lean_object* v_input_1530_; lean_object* v_messageHead_1531_; lean_object* v_messageCount_1532_; lean_object* v_bodyBytesRead_1533_; lean_object* v_headerBytesRead_1534_; uint8_t v_noMoreInput_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1543_; 
v_input_1530_ = lean_ctor_get(v_reader_1529_, 1);
v_messageHead_1531_ = lean_ctor_get(v_reader_1529_, 2);
v_messageCount_1532_ = lean_ctor_get(v_reader_1529_, 3);
v_bodyBytesRead_1533_ = lean_ctor_get(v_reader_1529_, 4);
v_headerBytesRead_1534_ = lean_ctor_get(v_reader_1529_, 5);
v_noMoreInput_1535_ = lean_ctor_get_uint8(v_reader_1529_, sizeof(void*)*6);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_reader_1529_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_reader_1529_, 0);
lean_dec(v_unused_1544_);
v___x_1537_ = v_reader_1529_;
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_headerBytesRead_1534_);
lean_inc(v_bodyBytesRead_1533_);
lean_inc(v_messageCount_1532_);
lean_inc(v_messageHead_1531_);
lean_inc(v_input_1530_);
lean_dec(v_reader_1529_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_input_1530_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_messageHead_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_messageCount_1532_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_bodyBytesRead_1533_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v_headerBytesRead_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*6, v_noMoreInput_1535_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1545_, lean_object* v_reader_1546_){
_start:
{
lean_object* v_input_1547_; lean_object* v_messageHead_1548_; lean_object* v_messageCount_1549_; lean_object* v_bodyBytesRead_1550_; lean_object* v_headerBytesRead_1551_; uint8_t v_noMoreInput_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_input_1547_ = lean_ctor_get(v_reader_1546_, 1);
v_messageHead_1548_ = lean_ctor_get(v_reader_1546_, 2);
v_messageCount_1549_ = lean_ctor_get(v_reader_1546_, 3);
v_bodyBytesRead_1550_ = lean_ctor_get(v_reader_1546_, 4);
v_headerBytesRead_1551_ = lean_ctor_get(v_reader_1546_, 5);
v_noMoreInput_1552_ = lean_ctor_get_uint8(v_reader_1546_, sizeof(void*)*6);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_reader_1546_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_reader_1546_, 0);
lean_dec(v_unused_1561_);
v___x_1554_ = v_reader_1546_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_headerBytesRead_1551_);
lean_inc(v_bodyBytesRead_1550_);
lean_inc(v_messageCount_1549_);
lean_inc(v_messageHead_1548_);
lean_inc(v_input_1547_);
lean_dec(v_reader_1546_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_input_1547_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_messageHead_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_messageCount_1549_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_bodyBytesRead_1550_);
lean_ctor_set(v_reuseFailAlloc_1559_, 5, v_headerBytesRead_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1559_, sizeof(void*)*6, v_noMoreInput_1552_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1562_, lean_object* v_reader_1563_){
_start:
{
uint8_t v_dir_boxed_1564_; lean_object* v_res_1565_; 
v_dir_boxed_1564_ = lean_unbox(v_dir_1562_);
v_res_1565_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1564_, v_reader_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object* v_reader_1566_){
_start:
{
lean_object* v_state_1567_; lean_object* v_input_1568_; lean_object* v_messageHead_1569_; lean_object* v_messageCount_1570_; lean_object* v_bodyBytesRead_1571_; lean_object* v_headerBytesRead_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_state_1567_ = lean_ctor_get(v_reader_1566_, 0);
v_input_1568_ = lean_ctor_get(v_reader_1566_, 1);
v_messageHead_1569_ = lean_ctor_get(v_reader_1566_, 2);
v_messageCount_1570_ = lean_ctor_get(v_reader_1566_, 3);
v_bodyBytesRead_1571_ = lean_ctor_get(v_reader_1566_, 4);
v_headerBytesRead_1572_ = lean_ctor_get(v_reader_1566_, 5);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_reader_1566_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v_reader_1566_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_headerBytesRead_1572_);
lean_inc(v_bodyBytesRead_1571_);
lean_inc(v_messageCount_1570_);
lean_inc(v_messageHead_1569_);
lean_inc(v_input_1568_);
lean_inc(v_state_1567_);
lean_dec(v_reader_1566_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint8_t v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = 1;
if (v_isShared_1575_ == 0)
{
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_state_1567_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_input_1568_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_messageHead_1569_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_messageCount_1570_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_bodyBytesRead_1571_);
lean_ctor_set(v_reuseFailAlloc_1579_, 5, v_headerBytesRead_1572_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_ctor_set_uint8(v___x_1578_, sizeof(void*)*6, v___x_1576_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t v_dir_1581_, lean_object* v_reader_1582_){
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
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object* v_dir_1597_, lean_object* v_reader_1598_){
_start:
{
uint8_t v_dir_boxed_1599_; lean_object* v_res_1600_; 
v_dir_boxed_1599_ = lean_unbox(v_dir_1597_);
v_res_1600_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_1599_, v_reader_1598_);
return v_res_1600_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1601_, lean_object* v_reader_1602_){
_start:
{
lean_object* v_messageHead_1603_; uint8_t v___x_1604_; 
v_messageHead_1603_ = lean_ctor_get(v_reader_1602_, 2);
v___x_1604_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1601_, v_messageHead_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1605_, lean_object* v_reader_1606_){
_start:
{
uint8_t v_dir_boxed_1607_; uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_dir_boxed_1607_ = lean_unbox(v_dir_1605_);
v_res_1608_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1607_, v_reader_1606_);
lean_dec_ref(v_reader_1606_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
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
