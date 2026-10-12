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
uint8_t l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(lean_object* v_x_313_, lean_object* v_x_314_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_313_ = stack[0].m_obj;
lean_object* v_x_314_ = stack[1].m_obj;
uint8_t v_res_321_;
v_res_321_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_x_313_, v_x_314_);
stack->m_num = v_res_321_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0___boxed(lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_x_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec(v_x_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(lean_object* v_xs_326_, lean_object* v_ys_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_zero_329_; uint8_t v_isZero_330_; 
v_zero_329_ = lean_unsigned_to_nat(0u);
v_isZero_330_ = lean_nat_dec_eq(v_x_328_, v_zero_329_);
if (v_isZero_330_ == 1)
{
lean_dec(v_x_328_);
return v_isZero_330_;
}
else
{
lean_object* v_one_331_; lean_object* v_n_332_; uint8_t v___y_334_; lean_object* v___x_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; uint8_t v___x_342_; 
v_one_331_ = lean_unsigned_to_nat(1u);
v_n_332_ = lean_nat_sub(v_x_328_, v_one_331_);
lean_dec(v_x_328_);
v___x_336_ = lean_array_fget_borrowed(v_xs_326_, v_n_332_);
v_fst_337_ = lean_ctor_get(v___x_336_, 0);
v_snd_338_ = lean_ctor_get(v___x_336_, 1);
v___x_339_ = lean_array_fget_borrowed(v_ys_327_, v_n_332_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
v_snd_341_ = lean_ctor_get(v___x_339_, 1);
v___x_342_ = l_Std_Http_Chunk_instBEqExtensionName_beq(v_fst_337_, v_fst_340_);
if (v___x_342_ == 0)
{
v___y_334_ = v___x_342_;
goto v___jp_333_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = l_instBEqOption_beq___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__0(v_snd_338_, v_snd_341_);
v___y_334_ = v___x_343_;
goto v___jp_333_;
}
v___jp_333_:
{
if (v___y_334_ == 0)
{
lean_dec(v_n_332_);
return v___y_334_;
}
else
{
v_x_328_ = v_n_332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_326_ = stack[0].m_obj;
lean_object* v_ys_327_ = stack[1].m_obj;
lean_object* v_x_328_ = stack[2].m_obj;
uint8_t v_res_344_;
v_res_344_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_326_, v_ys_327_, v_x_328_);
stack->m_num = v_res_344_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg___boxed(lean_object* v_xs_345_, lean_object* v_ys_346_, lean_object* v_x_347_){
_start:
{
uint8_t v_res_348_; lean_object* v_r_349_; 
v_res_348_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_345_, v_ys_346_, v_x_347_);
lean_dec_ref(v_ys_346_);
lean_dec_ref(v_xs_345_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(lean_object* v_x_350_, lean_object* v_x_351_){
_start:
{
switch(lean_obj_tag(v_x_350_))
{
case 0:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v_remaining_352_; lean_object* v_remaining_353_; uint8_t v___x_354_; 
v_remaining_352_ = lean_ctor_get(v_x_350_, 0);
v_remaining_353_ = lean_ctor_get(v_x_351_, 0);
v___x_354_ = lean_nat_dec_eq(v_remaining_352_, v_remaining_353_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = 0;
return v___x_355_;
}
}
case 1:
{
if (lean_obj_tag(v_x_351_) == 1)
{
uint8_t v___x_356_; 
v___x_356_ = 1;
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
}
case 2:
{
if (lean_obj_tag(v_x_351_) == 2)
{
lean_object* v_ext_358_; lean_object* v_remaining_359_; lean_object* v_ext_360_; lean_object* v_remaining_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_ext_358_ = lean_ctor_get(v_x_350_, 0);
v_remaining_359_ = lean_ctor_get(v_x_350_, 1);
v_ext_360_ = lean_ctor_get(v_x_351_, 0);
v_remaining_361_ = lean_ctor_get(v_x_351_, 1);
v___x_362_ = lean_array_get_size(v_ext_358_);
v___x_363_ = lean_array_get_size(v_ext_360_);
v___x_364_ = lean_nat_dec_eq(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
return v___x_364_;
}
else
{
uint8_t v___x_365_; 
v___x_365_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_ext_358_, v_ext_360_, v___x_362_);
if (v___x_365_ == 0)
{
return v___x_365_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_eq(v_remaining_359_, v_remaining_361_);
return v___x_366_;
}
}
}
else
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
}
default: 
{
if (lean_obj_tag(v_x_351_) == 3)
{
uint8_t v___x_368_; 
v___x_368_ = 1;
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_350_ = stack[0].m_obj;
lean_object* v_x_351_ = stack[1].m_obj;
uint8_t v_res_370_;
v_res_370_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_x_350_, v_x_351_);
stack->m_num = v_res_370_;
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
uint8_t l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(lean_object* v_xs_375_, lean_object* v_ys_376_, lean_object* v_hsz_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___redArg(v_xs_375_, v_ys_376_, v_x_378_);
return v___x_380_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_375_ = stack[0].m_obj;
lean_object* v_ys_376_ = stack[1].m_obj;
lean_object* v_x_378_ = stack[3].m_obj;
uint8_t v_res_381_;
v_res_381_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(v_xs_375_, v_ys_376_, lean_box(0), v_x_378_, lean_box(0));
stack->m_num = v_res_381_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1___boxed(lean_object* v_xs_382_, lean_object* v_ys_383_, lean_object* v_hsz_384_, lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Array_isEqvAux___at___00Std_Http_Protocol_H1_Reader_instBEqBodyState_beq_spec__1(v_xs_382_, v_ys_383_, v_hsz_384_, v_x_385_, v_x_386_);
lean_dec_ref(v_ys_383_);
lean_dec_ref(v_xs_382_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_tag_nat(v_x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg___boxed(lean_object* v_x_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___redArg(v_x_393_);
lean_dec(v_x_393_);
return v_res_394_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(uint8_t v_dir_395_, lean_object* v_x_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lean_obj_tag_nat(v_x_396_);
return v___x_397_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_395_ = stack[0].m_num;
lean_object* v_x_396_ = stack[1].m_obj;
lean_object* v_res_398_;
v_res_398_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(v_dir_395_, v_x_396_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl___boxed(lean_object* v_dir_399_, lean_object* v_x_400_){
_start:
{
uint8_t v_dir_boxed_401_; lean_object* v_res_402_; 
v_dir_boxed_401_ = lean_unbox(v_dir_399_);
v_res_402_ = l_Std_Http_Protocol_H1_Reader_State_ctorIdx___impl(v_dir_boxed_401_, v_x_400_);
lean_dec(v_x_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(lean_object* v_t_403_, lean_object* v_k_404_){
_start:
{
switch(lean_obj_tag(v_t_403_))
{
case 1:
{
lean_object* v_a_405_; lean_object* v___x_406_; 
v_a_405_ = lean_ctor_get(v_t_403_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v_t_403_, 1);
v___x_406_ = lean_apply_1(v_k_404_, v_a_405_);
return v___x_406_;
}
case 2:
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v_t_403_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v_t_403_, 1);
v___x_408_ = lean_apply_1(v_k_404_, v_a_407_);
return v___x_408_;
}
case 3:
{
lean_object* v_a_409_; lean_object* v___x_410_; 
v_a_409_ = lean_ctor_get(v_t_403_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v_t_403_, 1);
v___x_410_ = lean_apply_1(v_k_404_, v_a_409_);
return v___x_410_;
}
case 7:
{
lean_object* v_error_411_; lean_object* v___x_412_; 
v_error_411_ = lean_ctor_get(v_t_403_, 0);
lean_inc(v_error_411_);
lean_dec_ref_known(v_t_403_, 1);
v___x_412_ = lean_apply_1(v_k_404_, v_error_411_);
return v___x_412_;
}
default: 
{
lean_dec(v_t_403_);
return v_k_404_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim(uint8_t v_dir_413_, lean_object* v_motive_414_, lean_object* v_ctorIdx_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_k_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_416_, v_k_418_);
return v___x_419_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_ctorElim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_413_ = stack[0].m_num;
lean_object* v_ctorIdx_415_ = stack[2].m_obj;
lean_object* v_t_416_ = stack[3].m_obj;
lean_object* v_k_418_ = stack[5].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_413_, lean_box(0), v_ctorIdx_415_, v_t_416_, lean_box(0), v_k_418_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_ctorElim___boxed(lean_object* v_dir_421_, lean_object* v_motive_422_, lean_object* v_ctorIdx_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_k_426_){
_start:
{
uint8_t v_dir_boxed_427_; lean_object* v_res_428_; 
v_dir_boxed_427_ = lean_unbox(v_dir_421_);
v_res_428_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim(v_dir_boxed_427_, v_motive_422_, v_ctorIdx_423_, v_t_424_, v_h_425_, v_k_426_);
lean_dec(v_ctorIdx_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___redArg(lean_object* v_t_429_, lean_object* v_needStartLine_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_429_, v_needStartLine_430_);
return v___x_431_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(uint8_t v_dir_432_, lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_needStartLine_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_434_, v_needStartLine_436_);
return v___x_437_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_432_ = stack[0].m_num;
lean_object* v_t_434_ = stack[2].m_obj;
lean_object* v_needStartLine_436_ = stack[4].m_obj;
lean_object* v_res_438_;
v_res_438_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_432_, lean_box(0), v_t_434_, lean_box(0), v_needStartLine_436_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim___boxed(lean_object* v_dir_439_, lean_object* v_motive_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_needStartLine_443_){
_start:
{
uint8_t v_dir_boxed_444_; lean_object* v_res_445_; 
v_dir_boxed_444_ = lean_unbox(v_dir_439_);
v_res_445_ = l_Std_Http_Protocol_H1_Reader_State_needStartLine_elim(v_dir_boxed_444_, v_motive_440_, v_t_441_, v_h_442_, v_needStartLine_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___redArg(lean_object* v_t_446_, lean_object* v_needHeader_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_446_, v_needHeader_447_);
return v___x_448_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(uint8_t v_dir_449_, lean_object* v_motive_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_needHeader_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_451_, v_needHeader_453_);
return v___x_454_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_needHeader_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_449_ = stack[0].m_num;
lean_object* v_t_451_ = stack[2].m_obj;
lean_object* v_needHeader_453_ = stack[4].m_obj;
lean_object* v_res_455_;
v_res_455_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_449_, lean_box(0), v_t_451_, lean_box(0), v_needHeader_453_);
stack->m_obj
 = v_res_455_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_needHeader_elim___boxed(lean_object* v_dir_456_, lean_object* v_motive_457_, lean_object* v_t_458_, lean_object* v_h_459_, lean_object* v_needHeader_460_){
_start:
{
uint8_t v_dir_boxed_461_; lean_object* v_res_462_; 
v_dir_boxed_461_ = lean_unbox(v_dir_456_);
v_res_462_ = l_Std_Http_Protocol_H1_Reader_State_needHeader_elim(v_dir_boxed_461_, v_motive_457_, v_t_458_, v_h_459_, v_needHeader_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___redArg(lean_object* v_t_463_, lean_object* v_readBody_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_463_, v_readBody_464_);
return v___x_465_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim(uint8_t v_dir_466_, lean_object* v_motive_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_readBody_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_468_, v_readBody_470_);
return v___x_471_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_readBody_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_466_ = stack[0].m_num;
lean_object* v_t_468_ = stack[2].m_obj;
lean_object* v_readBody_470_ = stack[4].m_obj;
lean_object* v_res_472_;
v_res_472_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_466_, lean_box(0), v_t_468_, lean_box(0), v_readBody_470_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_readBody_elim___boxed(lean_object* v_dir_473_, lean_object* v_motive_474_, lean_object* v_t_475_, lean_object* v_h_476_, lean_object* v_readBody_477_){
_start:
{
uint8_t v_dir_boxed_478_; lean_object* v_res_479_; 
v_dir_boxed_478_ = lean_unbox(v_dir_473_);
v_res_479_ = l_Std_Http_Protocol_H1_Reader_State_readBody_elim(v_dir_boxed_478_, v_motive_474_, v_t_475_, v_h_476_, v_readBody_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim___redArg(lean_object* v_t_480_, lean_object* v_continue_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_480_, v_continue_481_);
return v___x_482_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_continue_elim(uint8_t v_dir_483_, lean_object* v_motive_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_continue_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_485_, v_continue_487_);
return v___x_488_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_continue_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_483_ = stack[0].m_num;
lean_object* v_t_485_ = stack[2].m_obj;
lean_object* v_continue_487_ = stack[4].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Std_Http_Protocol_H1_Reader_State_continue_elim(v_dir_483_, lean_box(0), v_t_485_, lean_box(0), v_continue_487_);
stack->m_obj
 = v_res_489_;
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
lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim(uint8_t v_dir_500_, lean_object* v_motive_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_pending_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_502_, v_pending_504_);
return v___x_505_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_pending_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_500_ = stack[0].m_num;
lean_object* v_t_502_ = stack[2].m_obj;
lean_object* v_pending_504_ = stack[4].m_obj;
lean_object* v_res_506_;
v_res_506_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_500_, lean_box(0), v_t_502_, lean_box(0), v_pending_504_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_pending_elim___boxed(lean_object* v_dir_507_, lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_pending_511_){
_start:
{
uint8_t v_dir_boxed_512_; lean_object* v_res_513_; 
v_dir_boxed_512_ = lean_unbox(v_dir_507_);
v_res_513_ = l_Std_Http_Protocol_H1_Reader_State_pending_elim(v_dir_boxed_512_, v_motive_508_, v_t_509_, v_h_510_, v_pending_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___redArg(lean_object* v_t_514_, lean_object* v_complete_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_514_, v_complete_515_);
return v___x_516_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim(uint8_t v_dir_517_, lean_object* v_motive_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_complete_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_519_, v_complete_521_);
return v___x_522_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_complete_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_517_ = stack[0].m_num;
lean_object* v_t_519_ = stack[2].m_obj;
lean_object* v_complete_521_ = stack[4].m_obj;
lean_object* v_res_523_;
v_res_523_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_517_, lean_box(0), v_t_519_, lean_box(0), v_complete_521_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_complete_elim___boxed(lean_object* v_dir_524_, lean_object* v_motive_525_, lean_object* v_t_526_, lean_object* v_h_527_, lean_object* v_complete_528_){
_start:
{
uint8_t v_dir_boxed_529_; lean_object* v_res_530_; 
v_dir_boxed_529_ = lean_unbox(v_dir_524_);
v_res_530_ = l_Std_Http_Protocol_H1_Reader_State_complete_elim(v_dir_boxed_529_, v_motive_525_, v_t_526_, v_h_527_, v_complete_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___redArg(lean_object* v_t_531_, lean_object* v_closed_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_531_, v_closed_532_);
return v___x_533_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim(uint8_t v_dir_534_, lean_object* v_motive_535_, lean_object* v_t_536_, lean_object* v_h_537_, lean_object* v_closed_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_536_, v_closed_538_);
return v___x_539_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_closed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_534_ = stack[0].m_num;
lean_object* v_t_536_ = stack[2].m_obj;
lean_object* v_closed_538_ = stack[4].m_obj;
lean_object* v_res_540_;
v_res_540_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_534_, lean_box(0), v_t_536_, lean_box(0), v_closed_538_);
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_closed_elim___boxed(lean_object* v_dir_541_, lean_object* v_motive_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_closed_545_){
_start:
{
uint8_t v_dir_boxed_546_; lean_object* v_res_547_; 
v_dir_boxed_546_ = lean_unbox(v_dir_541_);
v_res_547_ = l_Std_Http_Protocol_H1_Reader_State_closed_elim(v_dir_boxed_546_, v_motive_542_, v_t_543_, v_h_544_, v_closed_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___redArg(lean_object* v_t_548_, lean_object* v_failed_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_548_, v_failed_549_);
return v___x_550_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim(uint8_t v_dir_551_, lean_object* v_motive_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_failed_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Std_Http_Protocol_H1_Reader_State_ctorElim___redArg(v_t_553_, v_failed_555_);
return v___x_556_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_State_failed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_551_ = stack[0].m_num;
lean_object* v_t_553_ = stack[2].m_obj;
lean_object* v_failed_555_ = stack[4].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(v_dir_551_, lean_box(0), v_t_553_, lean_box(0), v_failed_555_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_State_failed_elim___boxed(lean_object* v_dir_558_, lean_object* v_motive_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_failed_562_){
_start:
{
uint8_t v_dir_boxed_563_; lean_object* v_res_564_; 
v_dir_boxed_563_ = lean_unbox(v_dir_558_);
v_res_564_ = l_Std_Http_Protocol_H1_Reader_State_failed_elim(v_dir_boxed_563_, v_motive_559_, v_t_560_, v_h_561_, v_failed_562_);
return v_res_564_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg(){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_box(0);
return v___x_566_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_567_;
v_res_567_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg___boxed(lean_object* v___dummy_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___redArg();
return v_res_569_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(uint8_t v_dir_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instInhabitedState_default_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_570_ = stack[0].m_num;
lean_object* v_res_572_;
v_res_572_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_570_);
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState_default___boxed(lean_object* v_dir_573_){
_start:
{
uint8_t v_dir_boxed_574_; lean_object* v_res_575_; 
v_dir_boxed_574_ = lean_unbox(v_dir_573_);
v_res_575_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState_default(v_dir_boxed_574_);
return v_res_575_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg(){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = lean_box(0);
return v___x_577_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_578_;
v_res_578_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg___boxed(lean_object* v___dummy_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState___redArg();
return v_res_580_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState(uint8_t v_a_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_box(0);
return v___x_582_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instInhabitedState_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_581_ = stack[0].m_num;
lean_object* v_res_583_;
v_res_583_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_581_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instInhabitedState___boxed(lean_object* v_a_584_){
_start:
{
uint8_t v_a_12__boxed_585_; lean_object* v_res_586_; 
v_a_12__boxed_585_ = lean_unbox(v_a_584_);
v_res_586_ = l_Std_Http_Protocol_H1_Reader_instInhabitedState(v_a_12__boxed_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(lean_object* v_x_623_, lean_object* v_prec_624_){
_start:
{
lean_object* v___y_626_; lean_object* v___y_633_; lean_object* v___y_640_; lean_object* v___y_647_; 
switch(lean_obj_tag(v_x_623_))
{
case 0:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(1024u);
v___x_654_ = lean_nat_dec_le(v___x_653_, v_prec_624_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_647_ = v___x_655_;
goto v___jp_646_;
}
else
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_647_ = v___x_656_;
goto v___jp_646_;
}
}
case 1:
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_677_; 
v_a_657_ = lean_ctor_get(v_x_623_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_677_ == 0)
{
v___x_659_ = v_x_623_;
v_isShared_660_ = v_isSharedCheck_677_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v_x_623_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_677_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___y_662_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(1024u);
v___x_674_ = lean_nat_dec_le(v___x_673_, v_prec_624_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_662_ = v___x_675_;
goto v___jp_661_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_662_ = v___x_676_;
goto v___jp_661_;
}
v___jp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_663_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__10));
v___x_664_ = l_Nat_reprFast(v_a_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set_tag(v___x_659_, 3);
lean_ctor_set(v___x_659_, 0, v___x_664_);
v___x_666_ = v___x_659_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_672_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_663_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v___y_662_);
v___x_668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_668_, 0, v___y_662_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = 0;
v___x_670_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set_uint8(v___x_670_, sizeof(void*)*1, v___x_669_);
v___x_671_ = l_Repr_addAppParen(v___x_670_, v_prec_624_);
return v___x_671_;
}
}
}
}
case 2:
{
lean_object* v_a_678_; lean_object* v___y_680_; lean_object* v___x_689_; uint8_t v___x_690_; 
v_a_678_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v_x_623_, 1);
v___x_689_ = lean_unsigned_to_nat(1024u);
v___x_690_ = lean_nat_dec_le(v___x_689_, v_prec_624_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_680_ = v___x_691_;
goto v___jp_679_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_680_ = v___x_692_;
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_681_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__13));
v___x_682_ = lean_unsigned_to_nat(1024u);
v___x_683_ = l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr(v_a_678_, v___x_682_);
v___x_684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_681_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
lean_inc(v___y_680_);
v___x_685_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_685_, 0, v___y_680_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = 0;
v___x_687_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_687_, 0, v___x_685_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*1, v___x_686_);
v___x_688_ = l_Repr_addAppParen(v___x_687_, v_prec_624_);
return v___x_688_;
}
}
case 3:
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___y_696_; uint8_t v___x_704_; 
v_a_693_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v_x_623_, 1);
v___x_694_ = lean_unsigned_to_nat(1024u);
v___x_704_ = lean_nat_dec_le(v___x_694_, v_prec_624_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_696_ = v___x_705_;
goto v___jp_695_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_696_ = v___x_706_;
goto v___jp_695_;
}
v___jp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_697_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__16));
v___x_698_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_a_693_, v___x_694_);
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_inc(v___y_696_);
v___x_700_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_700_, 0, v___y_696_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = 0;
v___x_702_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v___x_701_);
v___x_703_ = l_Repr_addAppParen(v___x_702_, v_prec_624_);
return v___x_703_;
}
}
case 4:
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(1024u);
v___x_708_ = lean_nat_dec_le(v___x_707_, v_prec_624_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_640_ = v___x_709_;
goto v___jp_639_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_640_ = v___x_710_;
goto v___jp_639_;
}
}
case 5:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(1024u);
v___x_712_ = lean_nat_dec_le(v___x_711_, v_prec_624_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_633_ = v___x_713_;
goto v___jp_632_;
}
else
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_633_ = v___x_714_;
goto v___jp_632_;
}
}
case 6:
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(1024u);
v___x_716_ = lean_nat_dec_le(v___x_715_, v_prec_624_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_626_ = v___x_717_;
goto v___jp_625_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_626_ = v___x_718_;
goto v___jp_625_;
}
}
default: 
{
lean_object* v_error_719_; lean_object* v___y_721_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_error_719_ = lean_ctor_get(v_x_623_, 0);
lean_inc(v_error_719_);
lean_dec_ref_known(v_x_623_, 1);
v___x_730_ = lean_unsigned_to_nat(1024u);
v___x_731_ = lean_nat_dec_le(v___x_730_, v_prec_624_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__7);
v___y_721_ = v___x_732_;
goto v___jp_720_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = lean_obj_once(&l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8, &l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8_once, _init_l_Std_Http_Protocol_H1_Reader_instReprBodyState_repr___closed__8);
v___y_721_ = v___x_733_;
goto v___jp_720_;
}
v___jp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_722_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__19));
v___x_723_ = lean_unsigned_to_nat(1024u);
v___x_724_ = l_Std_Http_Protocol_H1_instReprError_repr(v_error_719_, v___x_723_);
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_722_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_inc(v___y_721_);
v___x_726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_726_, 0, v___y_721_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = 0;
v___x_728_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*1, v___x_727_);
v___x_729_ = l_Repr_addAppParen(v___x_728_, v_prec_624_);
return v___x_729_;
}
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_627_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__1));
lean_inc(v___y_626_);
v___x_628_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_628_, 0, v___y_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = 0;
v___x_630_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*1, v___x_629_);
v___x_631_ = l_Repr_addAppParen(v___x_630_, v_prec_624_);
return v___x_631_;
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_634_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__3));
lean_inc(v___y_633_);
v___x_635_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_635_, 0, v___y_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = 0;
v___x_637_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*1, v___x_636_);
v___x_638_ = l_Repr_addAppParen(v___x_637_, v_prec_624_);
return v___x_638_;
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_641_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__5));
lean_inc(v___y_640_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___y_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = 0;
v___x_644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*1, v___x_643_);
v___x_645_ = l_Repr_addAppParen(v___x_644_, v_prec_624_);
return v___x_645_;
}
v___jp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_648_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___closed__7));
lean_inc(v___y_647_);
v___x_649_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_649_, 0, v___y_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = 0;
v___x_651_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*1, v___x_650_);
v___x_652_ = l_Repr_addAppParen(v___x_651_, v_prec_624_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg___boxed(lean_object* v_x_734_, lean_object* v_prec_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_734_, v_prec_735_);
lean_dec(v_prec_735_);
return v_res_736_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr(uint8_t v_dir_737_, lean_object* v_x_738_, lean_object* v_prec_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr___redArg(v_x_738_, v_prec_739_);
return v___x_740_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instReprState_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_737_ = stack[0].m_num;
lean_object* v_x_738_ = stack[1].m_obj;
lean_object* v_prec_739_ = stack[2].m_obj;
lean_object* v_res_741_;
v_res_741_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_737_, v_x_738_, v_prec_739_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed(lean_object* v_dir_742_, lean_object* v_x_743_, lean_object* v_prec_744_){
_start:
{
uint8_t v_dir_1025__boxed_745_; lean_object* v_res_746_; 
v_dir_1025__boxed_745_ = lean_unbox(v_dir_742_);
v_res_746_ = l_Std_Http_Protocol_H1_Reader_instReprState_repr(v_dir_1025__boxed_745_, v_x_743_, v_prec_744_);
lean_dec(v_prec_744_);
return v_res_746_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instReprState(uint8_t v_dir_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_box(v_dir_747_);
v___x_749_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instReprState_repr___boxed), 3, 1);
lean_closure_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instReprState_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_747_ = stack[0].m_num;
lean_object* v_res_750_;
v_res_750_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_747_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instReprState___boxed(lean_object* v_dir_751_){
_start:
{
uint8_t v_dir_5__boxed_752_; lean_object* v_res_753_; 
v_dir_5__boxed_752_ = lean_unbox(v_dir_751_);
v_res_753_ = l_Std_Http_Protocol_H1_Reader_instReprState(v_dir_5__boxed_752_);
return v_res_753_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
switch(lean_obj_tag(v_x_754_))
{
case 0:
{
if (lean_obj_tag(v_x_755_) == 0)
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
case 1:
{
if (lean_obj_tag(v_x_755_) == 1)
{
lean_object* v_a_758_; lean_object* v_a_759_; uint8_t v___x_760_; 
v_a_758_ = lean_ctor_get(v_x_754_, 0);
v_a_759_ = lean_ctor_get(v_x_755_, 0);
v___x_760_ = lean_nat_dec_eq(v_a_758_, v_a_759_);
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
case 2:
{
if (lean_obj_tag(v_x_755_) == 2)
{
lean_object* v_a_762_; lean_object* v_a_763_; uint8_t v___x_764_; 
v_a_762_ = lean_ctor_get(v_x_754_, 0);
v_a_763_ = lean_ctor_get(v_x_755_, 0);
v___x_764_ = l_Std_Http_Protocol_H1_Reader_instBEqBodyState_beq(v_a_762_, v_a_763_);
return v___x_764_;
}
else
{
uint8_t v___x_765_; 
v___x_765_ = 0;
return v___x_765_;
}
}
case 3:
{
if (lean_obj_tag(v_x_755_) == 3)
{
lean_object* v_a_766_; lean_object* v_a_767_; 
v_a_766_ = lean_ctor_get(v_x_754_, 0);
v_a_767_ = lean_ctor_get(v_x_755_, 0);
v_x_754_ = v_a_766_;
v_x_755_ = v_a_767_;
goto _start;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = 0;
return v___x_769_;
}
}
case 4:
{
if (lean_obj_tag(v_x_755_) == 4)
{
uint8_t v___x_770_; 
v___x_770_ = 1;
return v___x_770_;
}
else
{
uint8_t v___x_771_; 
v___x_771_ = 0;
return v___x_771_;
}
}
case 5:
{
if (lean_obj_tag(v_x_755_) == 5)
{
uint8_t v___x_772_; 
v___x_772_ = 1;
return v___x_772_;
}
else
{
uint8_t v___x_773_; 
v___x_773_ = 0;
return v___x_773_;
}
}
case 6:
{
if (lean_obj_tag(v_x_755_) == 6)
{
uint8_t v___x_774_; 
v___x_774_ = 1;
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = 0;
return v___x_775_;
}
}
default: 
{
if (lean_obj_tag(v_x_755_) == 7)
{
lean_object* v_error_776_; lean_object* v_error_777_; uint8_t v___x_778_; 
v_error_776_ = lean_ctor_get(v_x_754_, 0);
v_error_777_ = lean_ctor_get(v_x_755_, 0);
v___x_778_ = l_Std_Http_Protocol_H1_instBEqError_beq(v_error_776_, v_error_777_);
return v___x_778_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_754_ = stack[0].m_obj;
lean_object* v_x_755_ = stack[1].m_obj;
uint8_t v_res_780_;
v_res_780_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_754_, v_x_755_);
stack->m_num = v_res_780_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg___boxed(lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_781_, v_x_782_);
lean_dec(v_x_782_);
lean_dec(v_x_781_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_instBEqState_beq(uint8_t v_dir_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq___redArg(v_x_786_, v_x_787_);
return v___x_788_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instBEqState_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_785_ = stack[0].m_num;
lean_object* v_x_786_ = stack[1].m_obj;
lean_object* v_x_787_ = stack[2].m_obj;
uint8_t v_res_789_;
v_res_789_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_785_, v_x_786_, v_x_787_);
stack->m_num = v_res_789_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed(lean_object* v_dir_790_, lean_object* v_x_791_, lean_object* v_x_792_){
_start:
{
uint8_t v_dir_211__boxed_793_; uint8_t v_res_794_; lean_object* v_r_795_; 
v_dir_211__boxed_793_ = lean_unbox(v_dir_790_);
v_res_794_ = l_Std_Http_Protocol_H1_Reader_instBEqState_beq(v_dir_211__boxed_793_, v_x_791_, v_x_792_);
lean_dec(v_x_792_);
lean_dec(v_x_791_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState(uint8_t v_dir_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_box(v_dir_796_);
v___x_798_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_instBEqState_beq___boxed), 3, 1);
lean_closure_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_instBEqState_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_796_ = stack[0].m_num;
lean_object* v_res_799_;
v_res_799_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_796_);
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_instBEqState___boxed(lean_object* v_dir_800_){
_start:
{
uint8_t v_dir_5__boxed_801_; lean_object* v_res_802_; 
v_dir_5__boxed_801_ = lean_unbox(v_dir_800_);
v_res_802_ = l_Std_Http_Protocol_H1_Reader_instBEqState(v_dir_5__boxed_801_);
return v_res_802_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_isClosed___redArg(lean_object* v_reader_803_){
_start:
{
lean_object* v_state_804_; 
v_state_804_ = lean_ctor_get(v_reader_803_, 0);
if (lean_obj_tag(v_state_804_) == 6)
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
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_reader_803_ = stack[0].m_obj;
uint8_t v_res_807_;
v_res_807_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_803_);
stack->m_num = v_res_807_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___redArg___boxed(lean_object* v_reader_808_){
_start:
{
uint8_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Std_Http_Protocol_H1_Reader_isClosed___redArg(v_reader_808_);
lean_dec_ref(v_reader_808_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_isClosed(uint8_t v_dir_811_, lean_object* v_reader_812_){
_start:
{
lean_object* v_state_813_; 
v_state_813_ = lean_ctor_get(v_reader_812_, 0);
if (lean_obj_tag(v_state_813_) == 6)
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
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_isClosed_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_811_ = stack[0].m_num;
lean_object* v_reader_812_ = stack[1].m_obj;
uint8_t v_res_816_;
v_res_816_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_811_, v_reader_812_);
stack->m_num = v_res_816_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isClosed___boxed(lean_object* v_dir_817_, lean_object* v_reader_818_){
_start:
{
uint8_t v_dir_boxed_819_; uint8_t v_res_820_; lean_object* v_r_821_; 
v_dir_boxed_819_ = lean_unbox(v_dir_817_);
v_res_820_ = l_Std_Http_Protocol_H1_Reader_isClosed(v_dir_boxed_819_, v_reader_818_);
lean_dec_ref(v_reader_818_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_isComplete___redArg(lean_object* v_reader_822_){
_start:
{
lean_object* v_state_823_; 
v_state_823_ = lean_ctor_get(v_reader_822_, 0);
if (lean_obj_tag(v_state_823_) == 5)
{
uint8_t v___x_824_; 
v___x_824_ = 1;
return v___x_824_;
}
else
{
uint8_t v___x_825_; 
v___x_825_ = 0;
return v___x_825_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_isComplete___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_reader_822_ = stack[0].m_obj;
uint8_t v_res_826_;
v_res_826_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_822_);
stack->m_num = v_res_826_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___redArg___boxed(lean_object* v_reader_827_){
_start:
{
uint8_t v_res_828_; lean_object* v_r_829_; 
v_res_828_ = l_Std_Http_Protocol_H1_Reader_isComplete___redArg(v_reader_827_);
lean_dec_ref(v_reader_827_);
v_r_829_ = lean_box(v_res_828_);
return v_r_829_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_isComplete(uint8_t v_dir_830_, lean_object* v_reader_831_){
_start:
{
lean_object* v_state_832_; 
v_state_832_ = lean_ctor_get(v_reader_831_, 0);
if (lean_obj_tag(v_state_832_) == 5)
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
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_isComplete_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_830_ = stack[0].m_num;
lean_object* v_reader_831_ = stack[1].m_obj;
uint8_t v_res_835_;
v_res_835_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_830_, v_reader_831_);
stack->m_num = v_res_835_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_isComplete___boxed(lean_object* v_dir_836_, lean_object* v_reader_837_){
_start:
{
uint8_t v_dir_boxed_838_; uint8_t v_res_839_; lean_object* v_r_840_; 
v_dir_boxed_838_ = lean_unbox(v_dir_836_);
v_res_839_ = l_Std_Http_Protocol_H1_Reader_isComplete(v_dir_boxed_838_, v_reader_837_);
lean_dec_ref(v_reader_837_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(lean_object* v_reader_841_){
_start:
{
lean_object* v_state_842_; 
v_state_842_ = lean_ctor_get(v_reader_841_, 0);
if (lean_obj_tag(v_state_842_) == 7)
{
uint8_t v___x_843_; 
v___x_843_ = 1;
return v___x_843_;
}
else
{
uint8_t v___x_844_; 
v___x_844_ = 0;
return v___x_844_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_hasFailed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_reader_841_ = stack[0].m_obj;
uint8_t v_res_845_;
v_res_845_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_841_);
stack->m_num = v_res_845_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___redArg___boxed(lean_object* v_reader_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_Http_Protocol_H1_Reader_hasFailed___redArg(v_reader_846_);
lean_dec_ref(v_reader_846_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_hasFailed(uint8_t v_dir_849_, lean_object* v_reader_850_){
_start:
{
lean_object* v_state_851_; 
v_state_851_ = lean_ctor_get(v_reader_850_, 0);
if (lean_obj_tag(v_state_851_) == 7)
{
uint8_t v___x_852_; 
v___x_852_ = 1;
return v___x_852_;
}
else
{
uint8_t v___x_853_; 
v___x_853_ = 0;
return v___x_853_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_hasFailed_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_849_ = stack[0].m_num;
lean_object* v_reader_850_ = stack[1].m_obj;
uint8_t v_res_854_;
v_res_854_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_849_, v_reader_850_);
stack->m_num = v_res_854_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_hasFailed___boxed(lean_object* v_dir_855_, lean_object* v_reader_856_){
_start:
{
uint8_t v_dir_boxed_857_; uint8_t v_res_858_; lean_object* v_r_859_; 
v_dir_boxed_857_ = lean_unbox(v_dir_855_);
v_res_858_ = l_Std_Http_Protocol_H1_Reader_hasFailed(v_dir_boxed_857_, v_reader_856_);
lean_dec_ref(v_reader_856_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___redArg(lean_object* v_data_860_, lean_object* v_reader_861_){
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
lean_object* l_Std_Http_Protocol_H1_Reader_feed(uint8_t v_dir_890_, lean_object* v_data_891_, lean_object* v_reader_892_){
_start:
{
lean_object* v_input_893_; lean_object* v_state_894_; lean_object* v_messageHead_895_; lean_object* v_messageCount_896_; lean_object* v_bodyBytesRead_897_; lean_object* v_headerBytesRead_898_; uint8_t v_noMoreInput_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_920_; 
v_input_893_ = lean_ctor_get(v_reader_892_, 1);
v_state_894_ = lean_ctor_get(v_reader_892_, 0);
v_messageHead_895_ = lean_ctor_get(v_reader_892_, 2);
v_messageCount_896_ = lean_ctor_get(v_reader_892_, 3);
v_bodyBytesRead_897_ = lean_ctor_get(v_reader_892_, 4);
v_headerBytesRead_898_ = lean_ctor_get(v_reader_892_, 5);
v_noMoreInput_899_ = lean_ctor_get_uint8(v_reader_892_, sizeof(void*)*6);
v_isSharedCheck_920_ = !lean_is_exclusive(v_reader_892_);
if (v_isSharedCheck_920_ == 0)
{
v___x_901_ = v_reader_892_;
v_isShared_902_ = v_isSharedCheck_920_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_headerBytesRead_898_);
lean_inc(v_bodyBytesRead_897_);
lean_inc(v_messageCount_896_);
lean_inc(v_messageHead_895_);
lean_inc(v_input_893_);
lean_inc(v_state_894_);
lean_dec(v_reader_892_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_920_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_array_903_; lean_object* v_idx_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_array_903_ = lean_ctor_get(v_input_893_, 0);
lean_inc_ref(v_array_903_);
v_idx_904_ = lean_ctor_get(v_input_893_, 1);
lean_inc(v_idx_904_);
lean_dec_ref(v_input_893_);
v___x_905_ = lean_byte_array_size(v_array_903_);
v___x_906_ = lean_nat_dec_le(v___x_905_, v_idx_904_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_907_ = l_ByteArray_extract(v_array_903_, v_idx_904_, v___x_905_);
lean_dec_ref(v_array_903_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_byte_array_size(v___x_907_);
v___x_910_ = lean_byte_array_size(v_data_891_);
v___x_911_ = lean_byte_array_copy_slice(v_data_891_, v___x_908_, v___x_907_, v___x_909_, v___x_910_, v___x_906_);
lean_dec_ref(v_data_891_);
v___x_912_ = l_ByteArray_mkIterator(v___x_911_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_912_);
v___x_914_ = v___x_901_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_state_894_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_messageHead_895_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_messageCount_896_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_bodyBytesRead_897_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v_headerBytesRead_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*6, v_noMoreInput_899_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v_idx_904_);
lean_dec_ref(v_array_903_);
v___x_916_ = l_ByteArray_mkIterator(v_data_891_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_916_);
v___x_918_ = v___x_901_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_state_894_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_messageHead_895_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_messageCount_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_bodyBytesRead_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_headerBytesRead_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*6, v_noMoreInput_899_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_feed_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_890_ = stack[0].m_num;
lean_object* v_data_891_ = stack[1].m_obj;
lean_object* v_reader_892_ = stack[2].m_obj;
lean_object* v_res_921_;
v_res_921_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_890_, v_data_891_, v_reader_892_);
stack->m_obj
 = v_res_921_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_feed___boxed(lean_object* v_dir_922_, lean_object* v_data_923_, lean_object* v_reader_924_){
_start:
{
uint8_t v_dir_boxed_925_; lean_object* v_res_926_; 
v_dir_boxed_925_ = lean_unbox(v_dir_922_);
v_res_926_ = l_Std_Http_Protocol_H1_Reader_feed(v_dir_boxed_925_, v_data_923_, v_reader_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___redArg(lean_object* v_input_927_, lean_object* v_reader_928_){
_start:
{
lean_object* v_state_929_; lean_object* v_messageHead_930_; lean_object* v_messageCount_931_; lean_object* v_bodyBytesRead_932_; lean_object* v_headerBytesRead_933_; uint8_t v_noMoreInput_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_state_929_ = lean_ctor_get(v_reader_928_, 0);
v_messageHead_930_ = lean_ctor_get(v_reader_928_, 2);
v_messageCount_931_ = lean_ctor_get(v_reader_928_, 3);
v_bodyBytesRead_932_ = lean_ctor_get(v_reader_928_, 4);
v_headerBytesRead_933_ = lean_ctor_get(v_reader_928_, 5);
v_noMoreInput_934_ = lean_ctor_get_uint8(v_reader_928_, sizeof(void*)*6);
v_isSharedCheck_941_ = !lean_is_exclusive(v_reader_928_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_reader_928_, 1);
lean_dec(v_unused_942_);
v___x_936_ = v_reader_928_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_headerBytesRead_933_);
lean_inc(v_bodyBytesRead_932_);
lean_inc(v_messageCount_931_);
lean_inc(v_messageHead_930_);
lean_inc(v_state_929_);
lean_dec(v_reader_928_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v_input_927_);
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_state_929_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_input_927_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_messageHead_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_messageCount_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_bodyBytesRead_932_);
lean_ctor_set(v_reuseFailAlloc_940_, 5, v_headerBytesRead_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_940_, sizeof(void*)*6, v_noMoreInput_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_setInput(uint8_t v_dir_943_, lean_object* v_input_944_, lean_object* v_reader_945_){
_start:
{
lean_object* v_state_946_; lean_object* v_messageHead_947_; lean_object* v_messageCount_948_; lean_object* v_bodyBytesRead_949_; lean_object* v_headerBytesRead_950_; uint8_t v_noMoreInput_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
v_state_946_ = lean_ctor_get(v_reader_945_, 0);
v_messageHead_947_ = lean_ctor_get(v_reader_945_, 2);
v_messageCount_948_ = lean_ctor_get(v_reader_945_, 3);
v_bodyBytesRead_949_ = lean_ctor_get(v_reader_945_, 4);
v_headerBytesRead_950_ = lean_ctor_get(v_reader_945_, 5);
v_noMoreInput_951_ = lean_ctor_get_uint8(v_reader_945_, sizeof(void*)*6);
v_isSharedCheck_958_ = !lean_is_exclusive(v_reader_945_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_reader_945_, 1);
lean_dec(v_unused_959_);
v___x_953_ = v_reader_945_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_headerBytesRead_950_);
lean_inc(v_bodyBytesRead_949_);
lean_inc(v_messageCount_948_);
lean_inc(v_messageHead_947_);
lean_inc(v_state_946_);
lean_dec(v_reader_945_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_input_944_);
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_state_946_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_input_944_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_messageHead_947_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_messageCount_948_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v_bodyBytesRead_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 5, v_headerBytesRead_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_957_, sizeof(void*)*6, v_noMoreInput_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_setInput_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_943_ = stack[0].m_num;
lean_object* v_input_944_ = stack[1].m_obj;
lean_object* v_reader_945_ = stack[2].m_obj;
lean_object* v_res_960_;
v_res_960_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_943_, v_input_944_, v_reader_945_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setInput___boxed(lean_object* v_dir_961_, lean_object* v_input_962_, lean_object* v_reader_963_){
_start:
{
uint8_t v_dir_boxed_964_; lean_object* v_res_965_; 
v_dir_boxed_964_ = lean_unbox(v_dir_961_);
v_res_965_ = l_Std_Http_Protocol_H1_Reader_setInput(v_dir_boxed_964_, v_input_962_, v_reader_963_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___redArg(lean_object* v_messageHead_966_, lean_object* v_reader_967_){
_start:
{
lean_object* v_state_968_; lean_object* v_input_969_; lean_object* v_messageCount_970_; lean_object* v_bodyBytesRead_971_; lean_object* v_headerBytesRead_972_; uint8_t v_noMoreInput_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_state_968_ = lean_ctor_get(v_reader_967_, 0);
v_input_969_ = lean_ctor_get(v_reader_967_, 1);
v_messageCount_970_ = lean_ctor_get(v_reader_967_, 3);
v_bodyBytesRead_971_ = lean_ctor_get(v_reader_967_, 4);
v_headerBytesRead_972_ = lean_ctor_get(v_reader_967_, 5);
v_noMoreInput_973_ = lean_ctor_get_uint8(v_reader_967_, sizeof(void*)*6);
v_isSharedCheck_980_ = !lean_is_exclusive(v_reader_967_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v_reader_967_, 2);
lean_dec(v_unused_981_);
v___x_975_ = v_reader_967_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_headerBytesRead_972_);
lean_inc(v_bodyBytesRead_971_);
lean_inc(v_messageCount_970_);
lean_inc(v_input_969_);
lean_inc(v_state_968_);
lean_dec(v_reader_967_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 2, v_messageHead_966_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_state_968_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_input_969_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_messageHead_966_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_messageCount_970_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_bodyBytesRead_971_);
lean_ctor_set(v_reuseFailAlloc_979_, 5, v_headerBytesRead_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_979_, sizeof(void*)*6, v_noMoreInput_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead(uint8_t v_dir_982_, lean_object* v_messageHead_983_, lean_object* v_reader_984_){
_start:
{
lean_object* v_state_985_; lean_object* v_input_986_; lean_object* v_messageCount_987_; lean_object* v_bodyBytesRead_988_; lean_object* v_headerBytesRead_989_; uint8_t v_noMoreInput_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v_state_985_ = lean_ctor_get(v_reader_984_, 0);
v_input_986_ = lean_ctor_get(v_reader_984_, 1);
v_messageCount_987_ = lean_ctor_get(v_reader_984_, 3);
v_bodyBytesRead_988_ = lean_ctor_get(v_reader_984_, 4);
v_headerBytesRead_989_ = lean_ctor_get(v_reader_984_, 5);
v_noMoreInput_990_ = lean_ctor_get_uint8(v_reader_984_, sizeof(void*)*6);
v_isSharedCheck_997_ = !lean_is_exclusive(v_reader_984_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_reader_984_, 2);
lean_dec(v_unused_998_);
v___x_992_ = v_reader_984_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_headerBytesRead_989_);
lean_inc(v_bodyBytesRead_988_);
lean_inc(v_messageCount_987_);
lean_inc(v_input_986_);
lean_inc(v_state_985_);
lean_dec(v_reader_984_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v_messageHead_983_);
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_state_985_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_input_986_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_messageHead_983_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v_messageCount_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 4, v_bodyBytesRead_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 5, v_headerBytesRead_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_996_, sizeof(void*)*6, v_noMoreInput_990_);
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
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_setMessageHead_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_982_ = stack[0].m_num;
lean_object* v_messageHead_983_ = stack[1].m_obj;
lean_object* v_reader_984_ = stack[2].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_982_, v_messageHead_983_, v_reader_984_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_setMessageHead___boxed(lean_object* v_dir_1000_, lean_object* v_messageHead_1001_, lean_object* v_reader_1002_){
_start:
{
uint8_t v_dir_boxed_1003_; lean_object* v_res_1004_; 
v_dir_boxed_1003_ = lean_unbox(v_dir_1000_);
v_res_1004_ = l_Std_Http_Protocol_H1_Reader_setMessageHead(v_dir_boxed_1003_, v_messageHead_1001_, v_reader_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___lam__0(lean_object* v_i_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1006_) == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_1007_);
v___x_1009_ = lean_array_push(v___x_1008_, v_i_1005_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
else
{
lean_object* v_val_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
v_val_1011_ = lean_ctor_get(v_x_1006_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1013_ = v_x_1006_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_val_1011_);
lean_dec(v_x_1006_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_array_push(v_val_1011_, v_i_1005_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1017_ = v___x_1013_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_addHeader(uint8_t v_dir_1022_, lean_object* v_name_1023_, lean_object* v_value_1024_, lean_object* v_reader_1025_){
_start:
{
if (v_dir_1022_ == 0)
{
lean_object* v_messageHead_1026_; lean_object* v_state_1027_; lean_object* v_input_1028_; lean_object* v_messageCount_1029_; lean_object* v_bodyBytesRead_1030_; lean_object* v_headerBytesRead_1031_; uint8_t v_noMoreInput_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1068_; 
v_messageHead_1026_ = lean_ctor_get(v_reader_1025_, 2);
v_state_1027_ = lean_ctor_get(v_reader_1025_, 0);
v_input_1028_ = lean_ctor_get(v_reader_1025_, 1);
v_messageCount_1029_ = lean_ctor_get(v_reader_1025_, 3);
v_bodyBytesRead_1030_ = lean_ctor_get(v_reader_1025_, 4);
v_headerBytesRead_1031_ = lean_ctor_get(v_reader_1025_, 5);
v_noMoreInput_1032_ = lean_ctor_get_uint8(v_reader_1025_, sizeof(void*)*6);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_reader_1025_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1034_ = v_reader_1025_;
v_isShared_1035_ = v_isSharedCheck_1068_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_headerBytesRead_1031_);
lean_inc(v_bodyBytesRead_1030_);
lean_inc(v_messageCount_1029_);
lean_inc(v_messageHead_1026_);
lean_inc(v_input_1028_);
lean_inc(v_state_1027_);
lean_dec(v_reader_1025_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1068_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
uint8_t v_method_1036_; uint8_t v_version_1037_; lean_object* v_uri_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1065_; 
v_method_1036_ = lean_ctor_get_uint8(v_messageHead_1026_, sizeof(void*)*2);
v_version_1037_ = lean_ctor_get_uint8(v_messageHead_1026_, sizeof(void*)*2 + 1);
v_uri_1038_ = lean_ctor_get(v_messageHead_1026_, 0);
lean_inc(v_uri_1038_);
v___x_1039_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1022_, v_messageHead_1026_);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_messageHead_1026_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; lean_object* v_unused_1067_; 
v_unused_1066_ = lean_ctor_get(v_messageHead_1026_, 1);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_messageHead_1026_, 0);
lean_dec(v_unused_1067_);
v___x_1041_ = v_messageHead_1026_;
v_isShared_1042_ = v_isSharedCheck_1065_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v_messageHead_1026_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1065_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_entries_1043_; lean_object* v_indexes_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1064_; 
v_entries_1043_ = lean_ctor_get(v___x_1039_, 0);
v_indexes_1044_ = lean_ctor_get(v___x_1039_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1046_ = v___x_1039_;
v_isShared_1047_ = v_isSharedCheck_1064_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_indexes_1044_);
lean_inc(v_entries_1043_);
lean_dec(v___x_1039_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1064_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v_i_1050_; lean_object* v_f_1051_; lean_object* v___x_1052_; lean_object* v_entries_1053_; lean_object* v_indexes_1054_; lean_object* v___x_1056_; 
v___f_1048_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1049_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1050_ = lean_array_get_size(v_entries_1043_);
v_f_1051_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1051_, 0, v_i_1050_);
lean_inc_ref(v_name_1023_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v_name_1023_);
lean_ctor_set(v___x_1052_, 1, v_value_1024_);
v_entries_1053_ = lean_array_push(v_entries_1043_, v___x_1052_);
v_indexes_1054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1048_, v___f_1049_, v_indexes_1044_, v_name_1023_, v_f_1051_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_indexes_1054_);
lean_ctor_set(v___x_1046_, 0, v_entries_1053_);
v___x_1056_ = v___x_1046_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_entries_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_indexes_1054_);
v___x_1056_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___x_1056_);
v___x_1058_ = v___x_1041_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_uri_1038_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*2, v_method_1036_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*2 + 1, v_version_1037_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 2, v___x_1058_);
v___x_1060_ = v___x_1034_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_state_1027_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_input_1028_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_messageCount_1029_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_bodyBytesRead_1030_);
lean_ctor_set(v_reuseFailAlloc_1061_, 5, v_headerBytesRead_1031_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*6, v_noMoreInput_1032_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
}
}
else
{
lean_object* v_messageHead_1069_; lean_object* v_state_1070_; lean_object* v_input_1071_; lean_object* v_messageCount_1072_; lean_object* v_bodyBytesRead_1073_; lean_object* v_headerBytesRead_1074_; uint8_t v_noMoreInput_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1110_; 
v_messageHead_1069_ = lean_ctor_get(v_reader_1025_, 2);
v_state_1070_ = lean_ctor_get(v_reader_1025_, 0);
v_input_1071_ = lean_ctor_get(v_reader_1025_, 1);
v_messageCount_1072_ = lean_ctor_get(v_reader_1025_, 3);
v_bodyBytesRead_1073_ = lean_ctor_get(v_reader_1025_, 4);
v_headerBytesRead_1074_ = lean_ctor_get(v_reader_1025_, 5);
v_noMoreInput_1075_ = lean_ctor_get_uint8(v_reader_1025_, sizeof(void*)*6);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_reader_1025_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1077_ = v_reader_1025_;
v_isShared_1078_ = v_isSharedCheck_1110_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_headerBytesRead_1074_);
lean_inc(v_bodyBytesRead_1073_);
lean_inc(v_messageCount_1072_);
lean_inc(v_messageHead_1069_);
lean_inc(v_input_1071_);
lean_inc(v_state_1070_);
lean_dec(v_reader_1025_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1110_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_status_1079_; uint8_t v_version_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1107_; 
v_status_1079_ = lean_ctor_get(v_messageHead_1069_, 0);
lean_inc(v_status_1079_);
v_version_1080_ = lean_ctor_get_uint8(v_messageHead_1069_, sizeof(void*)*2);
v___x_1081_ = l_Std_Http_Protocol_H1_Message_Head_headers(v_dir_1022_, v_messageHead_1069_);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_messageHead_1069_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; 
v_unused_1108_ = lean_ctor_get(v_messageHead_1069_, 1);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v_messageHead_1069_, 0);
lean_dec(v_unused_1109_);
v___x_1083_ = v_messageHead_1069_;
v_isShared_1084_ = v_isSharedCheck_1107_;
goto v_resetjp_1082_;
}
else
{
lean_dec(v_messageHead_1069_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1107_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_entries_1085_; lean_object* v_indexes_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1106_; 
v_entries_1085_ = lean_ctor_get(v___x_1081_, 0);
v_indexes_1086_ = lean_ctor_get(v___x_1081_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1088_ = v___x_1081_;
v_isShared_1089_ = v_isSharedCheck_1106_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_indexes_1086_);
lean_inc(v_entries_1085_);
lean_dec(v___x_1081_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1106_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v_i_1092_; lean_object* v_f_1093_; lean_object* v___x_1094_; lean_object* v_entries_1095_; lean_object* v_indexes_1096_; lean_object* v___x_1098_; 
v___f_1090_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__0));
v___f_1091_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_addHeader___closed__1));
v_i_1092_ = lean_array_get_size(v_entries_1085_);
v_f_1093_ = lean_alloc_closure((void*)(l_Std_Http_Protocol_H1_Reader_addHeader___lam__0), 2, 1);
lean_closure_set(v_f_1093_, 0, v_i_1092_);
lean_inc_ref(v_name_1023_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_name_1023_);
lean_ctor_set(v___x_1094_, 1, v_value_1024_);
v_entries_1095_ = lean_array_push(v_entries_1085_, v___x_1094_);
v_indexes_1096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v___f_1090_, v___f_1091_, v_indexes_1086_, v_name_1023_, v_f_1093_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v_indexes_1096_);
lean_ctor_set(v___x_1088_, 0, v_entries_1095_);
v___x_1098_ = v___x_1088_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_entries_1095_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_indexes_1096_);
v___x_1098_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1098_);
v___x_1100_ = v___x_1083_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_status_1079_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*2, v_version_1080_);
v___x_1100_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 2, v___x_1100_);
v___x_1102_ = v___x_1077_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_state_1070_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_input_1071_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_messageCount_1072_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_bodyBytesRead_1073_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_headerBytesRead_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1103_, sizeof(void*)*6, v_noMoreInput_1075_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_addHeader_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1022_ = stack[0].m_num;
lean_object* v_name_1023_ = stack[1].m_obj;
lean_object* v_value_1024_ = stack[2].m_obj;
lean_object* v_reader_1025_ = stack[3].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_1022_, v_name_1023_, v_value_1024_, v_reader_1025_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeader___boxed(lean_object* v_dir_1112_, lean_object* v_name_1113_, lean_object* v_value_1114_, lean_object* v_reader_1115_){
_start:
{
uint8_t v_dir_boxed_1116_; lean_object* v_res_1117_; 
v_dir_boxed_1116_ = lean_unbox(v_dir_1112_);
v_res_1117_ = l_Std_Http_Protocol_H1_Reader_addHeader(v_dir_boxed_1116_, v_name_1113_, v_value_1114_, v_reader_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___redArg(lean_object* v_reader_1118_){
_start:
{
lean_object* v_input_1119_; lean_object* v_messageHead_1120_; lean_object* v_messageCount_1121_; lean_object* v_bodyBytesRead_1122_; lean_object* v_headerBytesRead_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1132_; 
v_input_1119_ = lean_ctor_get(v_reader_1118_, 1);
v_messageHead_1120_ = lean_ctor_get(v_reader_1118_, 2);
v_messageCount_1121_ = lean_ctor_get(v_reader_1118_, 3);
v_bodyBytesRead_1122_ = lean_ctor_get(v_reader_1118_, 4);
v_headerBytesRead_1123_ = lean_ctor_get(v_reader_1118_, 5);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_reader_1118_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; 
v_unused_1133_ = lean_ctor_get(v_reader_1118_, 0);
lean_dec(v_unused_1133_);
v___x_1125_ = v_reader_1118_;
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_headerBytesRead_1123_);
lean_inc(v_bodyBytesRead_1122_);
lean_inc(v_messageCount_1121_);
lean_inc(v_messageHead_1120_);
lean_inc(v_input_1119_);
lean_dec(v_reader_1118_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1132_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1130_; 
v___x_1127_ = lean_box(6);
v___x_1128_ = 1;
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_input_1119_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_messageHead_1120_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_messageCount_1121_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_bodyBytesRead_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 5, v_headerBytesRead_1123_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*6, v___x_1128_);
return v___x_1130_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_close(uint8_t v_dir_1134_, lean_object* v_reader_1135_){
_start:
{
lean_object* v_input_1136_; lean_object* v_messageHead_1137_; lean_object* v_messageCount_1138_; lean_object* v_bodyBytesRead_1139_; lean_object* v_headerBytesRead_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1149_; 
v_input_1136_ = lean_ctor_get(v_reader_1135_, 1);
v_messageHead_1137_ = lean_ctor_get(v_reader_1135_, 2);
v_messageCount_1138_ = lean_ctor_get(v_reader_1135_, 3);
v_bodyBytesRead_1139_ = lean_ctor_get(v_reader_1135_, 4);
v_headerBytesRead_1140_ = lean_ctor_get(v_reader_1135_, 5);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_reader_1135_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; 
v_unused_1150_ = lean_ctor_get(v_reader_1135_, 0);
lean_dec(v_unused_1150_);
v___x_1142_ = v_reader_1135_;
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_headerBytesRead_1140_);
lean_inc(v_bodyBytesRead_1139_);
lean_inc(v_messageCount_1138_);
lean_inc(v_messageHead_1137_);
lean_inc(v_input_1136_);
lean_dec(v_reader_1135_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1149_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; lean_object* v___x_1147_; 
v___x_1144_ = lean_box(6);
v___x_1145_ = 1;
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_input_1136_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_messageHead_1137_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_messageCount_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_bodyBytesRead_1139_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v_headerBytesRead_1140_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_ctor_set_uint8(v___x_1147_, sizeof(void*)*6, v___x_1145_);
return v___x_1147_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_close_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1134_ = stack[0].m_num;
lean_object* v_reader_1135_ = stack[1].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_1134_, v_reader_1135_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_close___boxed(lean_object* v_dir_1152_, lean_object* v_reader_1153_){
_start:
{
uint8_t v_dir_boxed_1154_; lean_object* v_res_1155_; 
v_dir_boxed_1154_ = lean_unbox(v_dir_1152_);
v_res_1155_ = l_Std_Http_Protocol_H1_Reader_close(v_dir_boxed_1154_, v_reader_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___redArg(lean_object* v_reader_1156_){
_start:
{
lean_object* v_input_1157_; lean_object* v_messageHead_1158_; lean_object* v_messageCount_1159_; lean_object* v_bodyBytesRead_1160_; lean_object* v_headerBytesRead_1161_; uint8_t v_noMoreInput_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1172_; 
v_input_1157_ = lean_ctor_get(v_reader_1156_, 1);
v_messageHead_1158_ = lean_ctor_get(v_reader_1156_, 2);
v_messageCount_1159_ = lean_ctor_get(v_reader_1156_, 3);
v_bodyBytesRead_1160_ = lean_ctor_get(v_reader_1156_, 4);
v_headerBytesRead_1161_ = lean_ctor_get(v_reader_1156_, 5);
v_noMoreInput_1162_ = lean_ctor_get_uint8(v_reader_1156_, sizeof(void*)*6);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_reader_1156_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_reader_1156_, 0);
lean_dec(v_unused_1173_);
v___x_1164_ = v_reader_1156_;
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_headerBytesRead_1161_);
lean_inc(v_bodyBytesRead_1160_);
lean_inc(v_messageCount_1159_);
lean_inc(v_messageHead_1158_);
lean_inc(v_input_1157_);
lean_dec(v_reader_1156_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1172_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1166_ = lean_box(5);
v___x_1167_ = lean_unsigned_to_nat(1u);
v___x_1168_ = lean_nat_add(v_messageCount_1159_, v___x_1167_);
lean_dec(v_messageCount_1159_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 3, v___x_1168_);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1170_ = v___x_1164_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_input_1157_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_messageHead_1158_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_bodyBytesRead_1160_);
lean_ctor_set(v_reuseFailAlloc_1171_, 5, v_headerBytesRead_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1171_, sizeof(void*)*6, v_noMoreInput_1162_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_markComplete(uint8_t v_dir_1174_, lean_object* v_reader_1175_){
_start:
{
lean_object* v_input_1176_; lean_object* v_messageHead_1177_; lean_object* v_messageCount_1178_; lean_object* v_bodyBytesRead_1179_; lean_object* v_headerBytesRead_1180_; uint8_t v_noMoreInput_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1191_; 
v_input_1176_ = lean_ctor_get(v_reader_1175_, 1);
v_messageHead_1177_ = lean_ctor_get(v_reader_1175_, 2);
v_messageCount_1178_ = lean_ctor_get(v_reader_1175_, 3);
v_bodyBytesRead_1179_ = lean_ctor_get(v_reader_1175_, 4);
v_headerBytesRead_1180_ = lean_ctor_get(v_reader_1175_, 5);
v_noMoreInput_1181_ = lean_ctor_get_uint8(v_reader_1175_, sizeof(void*)*6);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_reader_1175_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_reader_1175_, 0);
lean_dec(v_unused_1192_);
v___x_1183_ = v_reader_1175_;
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_headerBytesRead_1180_);
lean_inc(v_bodyBytesRead_1179_);
lean_inc(v_messageCount_1178_);
lean_inc(v_messageHead_1177_);
lean_inc(v_input_1176_);
lean_dec(v_reader_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1191_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1185_ = lean_box(5);
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_messageCount_1178_, v___x_1186_);
lean_dec(v_messageCount_1178_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 3, v___x_1187_);
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1189_ = v___x_1183_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_input_1176_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_messageHead_1177_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v_bodyBytesRead_1179_);
lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_headerBytesRead_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1190_, sizeof(void*)*6, v_noMoreInput_1181_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_markComplete_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1174_ = stack[0].m_num;
lean_object* v_reader_1175_ = stack[1].m_obj;
lean_object* v_res_1193_;
v_res_1193_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_1174_, v_reader_1175_);
stack->m_obj
 = v_res_1193_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markComplete___boxed(lean_object* v_dir_1194_, lean_object* v_reader_1195_){
_start:
{
uint8_t v_dir_boxed_1196_; lean_object* v_res_1197_; 
v_dir_boxed_1196_ = lean_unbox(v_dir_1194_);
v_res_1197_ = l_Std_Http_Protocol_H1_Reader_markComplete(v_dir_boxed_1196_, v_reader_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___redArg(lean_object* v_error_1198_, lean_object* v_reader_1199_){
_start:
{
lean_object* v_input_1200_; lean_object* v_messageHead_1201_; lean_object* v_messageCount_1202_; lean_object* v_bodyBytesRead_1203_; lean_object* v_headerBytesRead_1204_; uint8_t v_noMoreInput_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_input_1200_ = lean_ctor_get(v_reader_1199_, 1);
v_messageHead_1201_ = lean_ctor_get(v_reader_1199_, 2);
v_messageCount_1202_ = lean_ctor_get(v_reader_1199_, 3);
v_bodyBytesRead_1203_ = lean_ctor_get(v_reader_1199_, 4);
v_headerBytesRead_1204_ = lean_ctor_get(v_reader_1199_, 5);
v_noMoreInput_1205_ = lean_ctor_get_uint8(v_reader_1199_, sizeof(void*)*6);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_reader_1199_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v_reader_1199_, 0);
lean_dec(v_unused_1214_);
v___x_1207_ = v_reader_1199_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_headerBytesRead_1204_);
lean_inc(v_bodyBytesRead_1203_);
lean_inc(v_messageCount_1202_);
lean_inc(v_messageHead_1201_);
lean_inc(v_input_1200_);
lean_dec(v_reader_1199_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1209_, 0, v_error_1198_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_input_1200_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_messageHead_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_messageCount_1202_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_bodyBytesRead_1203_);
lean_ctor_set(v_reuseFailAlloc_1212_, 5, v_headerBytesRead_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*6, v_noMoreInput_1205_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_fail(uint8_t v_dir_1215_, lean_object* v_error_1216_, lean_object* v_reader_1217_){
_start:
{
lean_object* v_input_1218_; lean_object* v_messageHead_1219_; lean_object* v_messageCount_1220_; lean_object* v_bodyBytesRead_1221_; lean_object* v_headerBytesRead_1222_; uint8_t v_noMoreInput_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
v_input_1218_ = lean_ctor_get(v_reader_1217_, 1);
v_messageHead_1219_ = lean_ctor_get(v_reader_1217_, 2);
v_messageCount_1220_ = lean_ctor_get(v_reader_1217_, 3);
v_bodyBytesRead_1221_ = lean_ctor_get(v_reader_1217_, 4);
v_headerBytesRead_1222_ = lean_ctor_get(v_reader_1217_, 5);
v_noMoreInput_1223_ = lean_ctor_get_uint8(v_reader_1217_, sizeof(void*)*6);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_reader_1217_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_reader_1217_, 0);
lean_dec(v_unused_1232_);
v___x_1225_ = v_reader_1217_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_headerBytesRead_1222_);
lean_inc(v_bodyBytesRead_1221_);
lean_inc(v_messageCount_1220_);
lean_inc(v_messageHead_1219_);
lean_inc(v_input_1218_);
lean_dec(v_reader_1217_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_1227_, 0, v_error_1216_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_input_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_messageHead_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_messageCount_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_bodyBytesRead_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_headerBytesRead_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1230_, sizeof(void*)*6, v_noMoreInput_1223_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_fail_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1215_ = stack[0].m_num;
lean_object* v_error_1216_ = stack[1].m_obj;
lean_object* v_reader_1217_ = stack[2].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_1215_, v_error_1216_, v_reader_1217_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_fail___boxed(lean_object* v_dir_1234_, lean_object* v_error_1235_, lean_object* v_reader_1236_){
_start:
{
uint8_t v_dir_boxed_1237_; lean_object* v_res_1238_; 
v_dir_boxed_1237_ = lean_unbox(v_dir_1234_);
v_res_1238_ = l_Std_Http_Protocol_H1_Reader_fail(v_dir_boxed_1237_, v_error_1235_, v_reader_1236_);
return v_res_1238_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_reset(uint8_t v_dir_1239_, lean_object* v_reader_1240_){
_start:
{
lean_object* v_input_1241_; lean_object* v_messageCount_1242_; uint8_t v_noMoreInput_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1253_; 
v_input_1241_ = lean_ctor_get(v_reader_1240_, 1);
v_messageCount_1242_ = lean_ctor_get(v_reader_1240_, 3);
v_noMoreInput_1243_ = lean_ctor_get_uint8(v_reader_1240_, sizeof(void*)*6);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_reader_1240_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; lean_object* v_unused_1255_; lean_object* v_unused_1256_; lean_object* v_unused_1257_; 
v_unused_1254_ = lean_ctor_get(v_reader_1240_, 5);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_reader_1240_, 4);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_reader_1240_, 2);
lean_dec(v_unused_1256_);
v_unused_1257_ = lean_ctor_get(v_reader_1240_, 0);
lean_dec(v_unused_1257_);
v___x_1245_ = v_reader_1240_;
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_messageCount_1242_);
lean_inc(v_input_1241_);
lean_dec(v_reader_1240_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v_dir_1239_);
v___x_1249_ = lean_unsigned_to_nat(0u);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 5, v___x_1249_);
lean_ctor_set(v___x_1245_, 4, v___x_1249_);
lean_ctor_set(v___x_1245_, 2, v___x_1248_);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1251_ = v___x_1245_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_input_1241_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_messageCount_1242_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v___x_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*6, v_noMoreInput_1243_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_reset_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1239_ = stack[0].m_num;
lean_object* v_reader_1240_ = stack[1].m_obj;
lean_object* v_res_1258_;
v_res_1258_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_1239_, v_reader_1240_);
stack->m_obj
 = v_res_1258_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_reset___boxed(lean_object* v_dir_1259_, lean_object* v_reader_1260_){
_start:
{
uint8_t v_dir_boxed_1261_; lean_object* v_res_1262_; 
v_dir_boxed_1261_ = lean_unbox(v_dir_1259_);
v_res_1262_ = l_Std_Http_Protocol_H1_Reader_reset(v_dir_boxed_1261_, v_reader_1260_);
return v_res_1262_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(lean_object* v_reader_1263_){
_start:
{
lean_object* v_input_1264_; lean_object* v_state_1265_; uint8_t v_noMoreInput_1266_; lean_object* v_array_1267_; lean_object* v_idx_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_input_1264_ = lean_ctor_get(v_reader_1263_, 1);
v_state_1265_ = lean_ctor_get(v_reader_1263_, 0);
v_noMoreInput_1266_ = lean_ctor_get_uint8(v_reader_1263_, sizeof(void*)*6);
v_array_1267_ = lean_ctor_get(v_input_1264_, 0);
v_idx_1268_ = lean_ctor_get(v_input_1264_, 1);
v___x_1269_ = lean_byte_array_size(v_array_1267_);
v___x_1270_ = lean_nat_dec_le(v___x_1269_, v_idx_1268_);
if (v___x_1270_ == 0)
{
return v___x_1270_;
}
else
{
if (v_noMoreInput_1266_ == 0)
{
switch(lean_obj_tag(v_state_1265_))
{
case 5:
{
return v_noMoreInput_1266_;
}
case 6:
{
return v_noMoreInput_1266_;
}
case 7:
{
return v_noMoreInput_1266_;
}
case 3:
{
return v_noMoreInput_1266_;
}
default: 
{
return v___x_1270_;
}
}
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = 0;
return v___x_1271_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_reader_1263_ = stack[0].m_obj;
uint8_t v_res_1272_;
v_res_1272_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1263_);
stack->m_num = v_res_1272_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg___boxed(lean_object* v_reader_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput___redArg(v_reader_1273_);
lean_dec_ref(v_reader_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_needsMoreInput(uint8_t v_dir_1276_, lean_object* v_reader_1277_){
_start:
{
lean_object* v_input_1278_; lean_object* v_state_1279_; uint8_t v_noMoreInput_1280_; lean_object* v_array_1281_; lean_object* v_idx_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_input_1278_ = lean_ctor_get(v_reader_1277_, 1);
v_state_1279_ = lean_ctor_get(v_reader_1277_, 0);
v_noMoreInput_1280_ = lean_ctor_get_uint8(v_reader_1277_, sizeof(void*)*6);
v_array_1281_ = lean_ctor_get(v_input_1278_, 0);
v_idx_1282_ = lean_ctor_get(v_input_1278_, 1);
v___x_1283_ = lean_byte_array_size(v_array_1281_);
v___x_1284_ = lean_nat_dec_le(v___x_1283_, v_idx_1282_);
if (v___x_1284_ == 0)
{
return v___x_1284_;
}
else
{
if (v_noMoreInput_1280_ == 0)
{
switch(lean_obj_tag(v_state_1279_))
{
case 5:
{
return v_noMoreInput_1280_;
}
case 6:
{
return v_noMoreInput_1280_;
}
case 7:
{
return v_noMoreInput_1280_;
}
case 3:
{
return v_noMoreInput_1280_;
}
default: 
{
return v___x_1284_;
}
}
}
else
{
uint8_t v___x_1285_; 
v___x_1285_ = 0;
return v___x_1285_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_needsMoreInput_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1276_ = stack[0].m_num;
lean_object* v_reader_1277_ = stack[1].m_obj;
uint8_t v_res_1286_;
v_res_1286_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_1276_, v_reader_1277_);
stack->m_num = v_res_1286_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_needsMoreInput___boxed(lean_object* v_dir_1287_, lean_object* v_reader_1288_){
_start:
{
uint8_t v_dir_boxed_1289_; uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_dir_boxed_1289_ = lean_unbox(v_dir_1287_);
v_res_1290_ = l_Std_Http_Protocol_H1_Reader_needsMoreInput(v_dir_boxed_1289_, v_reader_1288_);
lean_dec_ref(v_reader_1288_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___redArg(lean_object* v_reader_1292_){
_start:
{
lean_object* v_state_1293_; 
v_state_1293_ = lean_ctor_get(v_reader_1292_, 0);
lean_inc(v_state_1293_);
lean_dec_ref(v_reader_1292_);
if (lean_obj_tag(v_state_1293_) == 7)
{
lean_object* v_error_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_error_1294_ = lean_ctor_get(v_state_1293_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_state_1293_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v_state_1293_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_error_1294_);
lean_dec(v_state_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 1);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_error_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v___x_1302_; 
lean_dec(v_state_1293_);
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_getError(uint8_t v_dir_1303_, lean_object* v_reader_1304_){
_start:
{
lean_object* v_state_1305_; 
v_state_1305_ = lean_ctor_get(v_reader_1304_, 0);
lean_inc(v_state_1305_);
lean_dec_ref(v_reader_1304_);
if (lean_obj_tag(v_state_1305_) == 7)
{
lean_object* v_error_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_error_1306_ = lean_ctor_get(v_state_1305_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_state_1305_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v_state_1305_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_error_1306_);
lean_dec(v_state_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set_tag(v___x_1308_, 1);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_error_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v___x_1314_; 
lean_dec(v_state_1305_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_getError_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1303_ = stack[0].m_num;
lean_object* v_reader_1304_ = stack[1].m_obj;
lean_object* v_res_1315_;
v_res_1315_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_1303_, v_reader_1304_);
stack->m_obj
 = v_res_1315_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_getError___boxed(lean_object* v_dir_1316_, lean_object* v_reader_1317_){
_start:
{
uint8_t v_dir_boxed_1318_; lean_object* v_res_1319_; 
v_dir_boxed_1318_ = lean_unbox(v_dir_1316_);
v_res_1319_ = l_Std_Http_Protocol_H1_Reader_getError(v_dir_boxed_1318_, v_reader_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(lean_object* v_reader_1320_){
_start:
{
lean_object* v_input_1321_; lean_object* v_array_1322_; lean_object* v_idx_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_input_1321_ = lean_ctor_get(v_reader_1320_, 1);
v_array_1322_ = lean_ctor_get(v_input_1321_, 0);
v_idx_1323_ = lean_ctor_get(v_input_1321_, 1);
v___x_1324_ = lean_byte_array_size(v_array_1322_);
v___x_1325_ = lean_nat_sub(v___x_1324_, v_idx_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg___boxed(lean_object* v_reader_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Std_Http_Protocol_H1_Reader_remainingBytes___redArg(v_reader_1326_);
lean_dec_ref(v_reader_1326_);
return v_res_1327_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes(uint8_t v_dir_1328_, lean_object* v_reader_1329_){
_start:
{
lean_object* v_input_1330_; lean_object* v_array_1331_; lean_object* v_idx_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_input_1330_ = lean_ctor_get(v_reader_1329_, 1);
v_array_1331_ = lean_ctor_get(v_input_1330_, 0);
v_idx_1332_ = lean_ctor_get(v_input_1330_, 1);
v___x_1333_ = lean_byte_array_size(v_array_1331_);
v___x_1334_ = lean_nat_sub(v___x_1333_, v_idx_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_remainingBytes_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1328_ = stack[0].m_num;
lean_object* v_reader_1329_ = stack[1].m_obj;
lean_object* v_res_1335_;
v_res_1335_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_1328_, v_reader_1329_);
stack->m_obj
 = v_res_1335_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_remainingBytes___boxed(lean_object* v_dir_1336_, lean_object* v_reader_1337_){
_start:
{
uint8_t v_dir_boxed_1338_; lean_object* v_res_1339_; 
v_dir_boxed_1338_ = lean_unbox(v_dir_1336_);
v_res_1339_ = l_Std_Http_Protocol_H1_Reader_remainingBytes(v_dir_boxed_1338_, v_reader_1337_);
lean_dec_ref(v_reader_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg(lean_object* v_n_1340_, lean_object* v_reader_1341_){
_start:
{
lean_object* v_input_1342_; lean_object* v_state_1343_; lean_object* v_messageHead_1344_; lean_object* v_messageCount_1345_; lean_object* v_bodyBytesRead_1346_; lean_object* v_headerBytesRead_1347_; uint8_t v_noMoreInput_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1365_; 
v_input_1342_ = lean_ctor_get(v_reader_1341_, 1);
v_state_1343_ = lean_ctor_get(v_reader_1341_, 0);
v_messageHead_1344_ = lean_ctor_get(v_reader_1341_, 2);
v_messageCount_1345_ = lean_ctor_get(v_reader_1341_, 3);
v_bodyBytesRead_1346_ = lean_ctor_get(v_reader_1341_, 4);
v_headerBytesRead_1347_ = lean_ctor_get(v_reader_1341_, 5);
v_noMoreInput_1348_ = lean_ctor_get_uint8(v_reader_1341_, sizeof(void*)*6);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_reader_1341_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1350_ = v_reader_1341_;
v_isShared_1351_ = v_isSharedCheck_1365_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_headerBytesRead_1347_);
lean_inc(v_bodyBytesRead_1346_);
lean_inc(v_messageCount_1345_);
lean_inc(v_messageHead_1344_);
lean_inc(v_input_1342_);
lean_inc(v_state_1343_);
lean_dec(v_reader_1341_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1365_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v_array_1352_; lean_object* v_idx_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1364_; 
v_array_1352_ = lean_ctor_get(v_input_1342_, 0);
v_idx_1353_ = lean_ctor_get(v_input_1342_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_input_1342_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1355_ = v_input_1342_;
v_isShared_1356_ = v_isSharedCheck_1364_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_idx_1353_);
lean_inc(v_array_1352_);
lean_dec(v_input_1342_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1364_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_nat_add(v_idx_1353_, v_n_1340_);
lean_dec(v_idx_1353_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 1, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_array_1352_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1359_);
v___x_1361_ = v___x_1350_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_state_1343_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_messageHead_1344_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_messageCount_1345_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_bodyBytesRead_1346_);
lean_ctor_set(v_reuseFailAlloc_1362_, 5, v_headerBytesRead_1347_);
lean_ctor_set_uint8(v_reuseFailAlloc_1362_, sizeof(void*)*6, v_noMoreInput_1348_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___redArg___boxed(lean_object* v_n_1366_, lean_object* v_reader_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_Http_Protocol_H1_Reader_advance___redArg(v_n_1366_, v_reader_1367_);
lean_dec(v_n_1366_);
return v_res_1368_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_advance(uint8_t v_dir_1369_, lean_object* v_n_1370_, lean_object* v_reader_1371_){
_start:
{
lean_object* v_input_1372_; lean_object* v_state_1373_; lean_object* v_messageHead_1374_; lean_object* v_messageCount_1375_; lean_object* v_bodyBytesRead_1376_; lean_object* v_headerBytesRead_1377_; uint8_t v_noMoreInput_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1395_; 
v_input_1372_ = lean_ctor_get(v_reader_1371_, 1);
v_state_1373_ = lean_ctor_get(v_reader_1371_, 0);
v_messageHead_1374_ = lean_ctor_get(v_reader_1371_, 2);
v_messageCount_1375_ = lean_ctor_get(v_reader_1371_, 3);
v_bodyBytesRead_1376_ = lean_ctor_get(v_reader_1371_, 4);
v_headerBytesRead_1377_ = lean_ctor_get(v_reader_1371_, 5);
v_noMoreInput_1378_ = lean_ctor_get_uint8(v_reader_1371_, sizeof(void*)*6);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_reader_1371_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1380_ = v_reader_1371_;
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_headerBytesRead_1377_);
lean_inc(v_bodyBytesRead_1376_);
lean_inc(v_messageCount_1375_);
lean_inc(v_messageHead_1374_);
lean_inc(v_input_1372_);
lean_inc(v_state_1373_);
lean_dec(v_reader_1371_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1395_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_array_1382_; lean_object* v_idx_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1394_; 
v_array_1382_ = lean_ctor_get(v_input_1372_, 0);
v_idx_1383_ = lean_ctor_get(v_input_1372_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_input_1372_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1385_ = v_input_1372_;
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_idx_1383_);
lean_inc(v_array_1382_);
lean_dec(v_input_1372_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1394_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_nat_add(v_idx_1383_, v_n_1370_);
lean_dec(v_idx_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 1, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_array_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1389_);
v___x_1391_ = v___x_1380_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_state_1373_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_messageHead_1374_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_messageCount_1375_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_bodyBytesRead_1376_);
lean_ctor_set(v_reuseFailAlloc_1392_, 5, v_headerBytesRead_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1392_, sizeof(void*)*6, v_noMoreInput_1378_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_advance_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1369_ = stack[0].m_num;
lean_object* v_n_1370_ = stack[1].m_obj;
lean_object* v_reader_1371_ = stack[2].m_obj;
lean_object* v_res_1396_;
v_res_1396_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_1369_, v_n_1370_, v_reader_1371_);
stack->m_obj
 = v_res_1396_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_advance___boxed(lean_object* v_dir_1397_, lean_object* v_n_1398_, lean_object* v_reader_1399_){
_start:
{
uint8_t v_dir_boxed_1400_; lean_object* v_res_1401_; 
v_dir_boxed_1400_ = lean_unbox(v_dir_1397_);
v_res_1401_ = l_Std_Http_Protocol_H1_Reader_advance(v_dir_boxed_1400_, v_n_1398_, v_reader_1399_);
lean_dec(v_n_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___redArg(lean_object* v_reader_1404_){
_start:
{
lean_object* v_input_1405_; lean_object* v_messageHead_1406_; lean_object* v_messageCount_1407_; uint8_t v_noMoreInput_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1417_; 
v_input_1405_ = lean_ctor_get(v_reader_1404_, 1);
v_messageHead_1406_ = lean_ctor_get(v_reader_1404_, 2);
v_messageCount_1407_ = lean_ctor_get(v_reader_1404_, 3);
v_noMoreInput_1408_ = lean_ctor_get_uint8(v_reader_1404_, sizeof(void*)*6);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_reader_1404_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; lean_object* v_unused_1419_; lean_object* v_unused_1420_; 
v_unused_1418_ = lean_ctor_get(v_reader_1404_, 5);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_reader_1404_, 4);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_reader_1404_, 0);
lean_dec(v_unused_1420_);
v___x_1410_ = v_reader_1404_;
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_messageCount_1407_);
lean_inc(v_messageHead_1406_);
lean_inc(v_input_1405_);
lean_dec(v_reader_1404_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 5, v___x_1412_);
lean_ctor_set(v___x_1410_, 4, v___x_1412_);
lean_ctor_set(v___x_1410_, 0, v___x_1413_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_input_1405_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_messageHead_1406_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_messageCount_1407_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1416_, 5, v___x_1412_);
lean_ctor_set_uint8(v_reuseFailAlloc_1416_, sizeof(void*)*6, v_noMoreInput_1408_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders(uint8_t v_dir_1421_, lean_object* v_reader_1422_){
_start:
{
lean_object* v_input_1423_; lean_object* v_messageHead_1424_; lean_object* v_messageCount_1425_; uint8_t v_noMoreInput_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1435_; 
v_input_1423_ = lean_ctor_get(v_reader_1422_, 1);
v_messageHead_1424_ = lean_ctor_get(v_reader_1422_, 2);
v_messageCount_1425_ = lean_ctor_get(v_reader_1422_, 3);
v_noMoreInput_1426_ = lean_ctor_get_uint8(v_reader_1422_, sizeof(void*)*6);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_reader_1422_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; 
v_unused_1436_ = lean_ctor_get(v_reader_1422_, 5);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_reader_1422_, 4);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_reader_1422_, 0);
lean_dec(v_unused_1438_);
v___x_1428_ = v_reader_1422_;
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_messageCount_1425_);
lean_inc(v_messageHead_1424_);
lean_inc(v_input_1423_);
lean_dec(v_reader_1422_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1435_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startHeaders___redArg___closed__0));
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 5, v___x_1430_);
lean_ctor_set(v___x_1428_, 4, v___x_1430_);
lean_ctor_set(v___x_1428_, 0, v___x_1431_);
v___x_1433_ = v___x_1428_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_input_1423_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_messageHead_1424_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_messageCount_1425_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1434_, 5, v___x_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1434_, sizeof(void*)*6, v_noMoreInput_1426_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_startHeaders_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1421_ = stack[0].m_num;
lean_object* v_reader_1422_ = stack[1].m_obj;
lean_object* v_res_1439_;
v_res_1439_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_1421_, v_reader_1422_);
stack->m_obj
 = v_res_1439_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startHeaders___boxed(lean_object* v_dir_1440_, lean_object* v_reader_1441_){
_start:
{
uint8_t v_dir_boxed_1442_; lean_object* v_res_1443_; 
v_dir_boxed_1442_ = lean_unbox(v_dir_1440_);
v_res_1443_ = l_Std_Http_Protocol_H1_Reader_startHeaders(v_dir_boxed_1442_, v_reader_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(lean_object* v_n_1444_, lean_object* v_reader_1445_){
_start:
{
lean_object* v_state_1446_; lean_object* v_input_1447_; lean_object* v_messageHead_1448_; lean_object* v_messageCount_1449_; lean_object* v_bodyBytesRead_1450_; lean_object* v_headerBytesRead_1451_; uint8_t v_noMoreInput_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1460_; 
v_state_1446_ = lean_ctor_get(v_reader_1445_, 0);
v_input_1447_ = lean_ctor_get(v_reader_1445_, 1);
v_messageHead_1448_ = lean_ctor_get(v_reader_1445_, 2);
v_messageCount_1449_ = lean_ctor_get(v_reader_1445_, 3);
v_bodyBytesRead_1450_ = lean_ctor_get(v_reader_1445_, 4);
v_headerBytesRead_1451_ = lean_ctor_get(v_reader_1445_, 5);
v_noMoreInput_1452_ = lean_ctor_get_uint8(v_reader_1445_, sizeof(void*)*6);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_reader_1445_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1454_ = v_reader_1445_;
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_headerBytesRead_1451_);
lean_inc(v_bodyBytesRead_1450_);
lean_inc(v_messageCount_1449_);
lean_inc(v_messageHead_1448_);
lean_inc(v_input_1447_);
lean_inc(v_state_1446_);
lean_dec(v_reader_1445_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_nat_add(v_bodyBytesRead_1450_, v_n_1444_);
lean_dec(v_bodyBytesRead_1450_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v___x_1456_);
v___x_1458_ = v___x_1454_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_state_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_input_1447_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_messageHead_1448_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_messageCount_1449_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v_headerBytesRead_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1459_, sizeof(void*)*6, v_noMoreInput_1452_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg___boxed(lean_object* v_n_1461_, lean_object* v_reader_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes___redArg(v_n_1461_, v_reader_1462_);
lean_dec(v_n_1461_);
return v_res_1463_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes(uint8_t v_dir_1464_, lean_object* v_n_1465_, lean_object* v_reader_1466_){
_start:
{
lean_object* v_state_1467_; lean_object* v_input_1468_; lean_object* v_messageHead_1469_; lean_object* v_messageCount_1470_; lean_object* v_bodyBytesRead_1471_; lean_object* v_headerBytesRead_1472_; uint8_t v_noMoreInput_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1481_; 
v_state_1467_ = lean_ctor_get(v_reader_1466_, 0);
v_input_1468_ = lean_ctor_get(v_reader_1466_, 1);
v_messageHead_1469_ = lean_ctor_get(v_reader_1466_, 2);
v_messageCount_1470_ = lean_ctor_get(v_reader_1466_, 3);
v_bodyBytesRead_1471_ = lean_ctor_get(v_reader_1466_, 4);
v_headerBytesRead_1472_ = lean_ctor_get(v_reader_1466_, 5);
v_noMoreInput_1473_ = lean_ctor_get_uint8(v_reader_1466_, sizeof(void*)*6);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_reader_1466_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1475_ = v_reader_1466_;
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_headerBytesRead_1472_);
lean_inc(v_bodyBytesRead_1471_);
lean_inc(v_messageCount_1470_);
lean_inc(v_messageHead_1469_);
lean_inc(v_input_1468_);
lean_inc(v_state_1467_);
lean_dec(v_reader_1466_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = lean_nat_add(v_bodyBytesRead_1471_, v_n_1465_);
lean_dec(v_bodyBytesRead_1471_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v___x_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_state_1467_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_input_1468_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_messageHead_1469_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_messageCount_1470_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v_headerBytesRead_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*6, v_noMoreInput_1473_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_addBodyBytes_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1464_ = stack[0].m_num;
lean_object* v_n_1465_ = stack[1].m_obj;
lean_object* v_reader_1466_ = stack[2].m_obj;
lean_object* v_res_1482_;
v_res_1482_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_1464_, v_n_1465_, v_reader_1466_);
stack->m_obj
 = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addBodyBytes___boxed(lean_object* v_dir_1483_, lean_object* v_n_1484_, lean_object* v_reader_1485_){
_start:
{
uint8_t v_dir_boxed_1486_; lean_object* v_res_1487_; 
v_dir_boxed_1486_ = lean_unbox(v_dir_1483_);
v_res_1487_ = l_Std_Http_Protocol_H1_Reader_addBodyBytes(v_dir_boxed_1486_, v_n_1484_, v_reader_1485_);
lean_dec(v_n_1484_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(lean_object* v_n_1488_, lean_object* v_reader_1489_){
_start:
{
lean_object* v_state_1490_; lean_object* v_input_1491_; lean_object* v_messageHead_1492_; lean_object* v_messageCount_1493_; lean_object* v_bodyBytesRead_1494_; lean_object* v_headerBytesRead_1495_; uint8_t v_noMoreInput_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1504_; 
v_state_1490_ = lean_ctor_get(v_reader_1489_, 0);
v_input_1491_ = lean_ctor_get(v_reader_1489_, 1);
v_messageHead_1492_ = lean_ctor_get(v_reader_1489_, 2);
v_messageCount_1493_ = lean_ctor_get(v_reader_1489_, 3);
v_bodyBytesRead_1494_ = lean_ctor_get(v_reader_1489_, 4);
v_headerBytesRead_1495_ = lean_ctor_get(v_reader_1489_, 5);
v_noMoreInput_1496_ = lean_ctor_get_uint8(v_reader_1489_, sizeof(void*)*6);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_reader_1489_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1498_ = v_reader_1489_;
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_headerBytesRead_1495_);
lean_inc(v_bodyBytesRead_1494_);
lean_inc(v_messageCount_1493_);
lean_inc(v_messageHead_1492_);
lean_inc(v_input_1491_);
lean_inc(v_state_1490_);
lean_dec(v_reader_1489_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_nat_add(v_headerBytesRead_1495_, v_n_1488_);
lean_dec(v_headerBytesRead_1495_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 5, v___x_1500_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_state_1490_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_input_1491_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_messageHead_1492_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_messageCount_1493_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_bodyBytesRead_1494_);
lean_ctor_set(v_reuseFailAlloc_1503_, 5, v___x_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1503_, sizeof(void*)*6, v_noMoreInput_1496_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg___boxed(lean_object* v_n_1505_, lean_object* v_reader_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes___redArg(v_n_1505_, v_reader_1506_);
lean_dec(v_n_1505_);
return v_res_1507_;
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes(uint8_t v_dir_1508_, lean_object* v_n_1509_, lean_object* v_reader_1510_){
_start:
{
lean_object* v_state_1511_; lean_object* v_input_1512_; lean_object* v_messageHead_1513_; lean_object* v_messageCount_1514_; lean_object* v_bodyBytesRead_1515_; lean_object* v_headerBytesRead_1516_; uint8_t v_noMoreInput_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v_state_1511_ = lean_ctor_get(v_reader_1510_, 0);
v_input_1512_ = lean_ctor_get(v_reader_1510_, 1);
v_messageHead_1513_ = lean_ctor_get(v_reader_1510_, 2);
v_messageCount_1514_ = lean_ctor_get(v_reader_1510_, 3);
v_bodyBytesRead_1515_ = lean_ctor_get(v_reader_1510_, 4);
v_headerBytesRead_1516_ = lean_ctor_get(v_reader_1510_, 5);
v_noMoreInput_1517_ = lean_ctor_get_uint8(v_reader_1510_, sizeof(void*)*6);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_reader_1510_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v_reader_1510_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_headerBytesRead_1516_);
lean_inc(v_bodyBytesRead_1515_);
lean_inc(v_messageCount_1514_);
lean_inc(v_messageHead_1513_);
lean_inc(v_input_1512_);
lean_inc(v_state_1511_);
lean_dec(v_reader_1510_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_nat_add(v_headerBytesRead_1516_, v_n_1509_);
lean_dec(v_headerBytesRead_1516_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 5, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_state_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_input_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_messageHead_1513_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_messageCount_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_bodyBytesRead_1515_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v___x_1521_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*6, v_noMoreInput_1517_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_addHeaderBytes_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1508_ = stack[0].m_num;
lean_object* v_n_1509_ = stack[1].m_obj;
lean_object* v_reader_1510_ = stack[2].m_obj;
lean_object* v_res_1526_;
v_res_1526_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_1508_, v_n_1509_, v_reader_1510_);
stack->m_obj
 = v_res_1526_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_addHeaderBytes___boxed(lean_object* v_dir_1527_, lean_object* v_n_1528_, lean_object* v_reader_1529_){
_start:
{
uint8_t v_dir_boxed_1530_; lean_object* v_res_1531_; 
v_dir_boxed_1530_ = lean_unbox(v_dir_1527_);
v_res_1531_ = l_Std_Http_Protocol_H1_Reader_addHeaderBytes(v_dir_boxed_1530_, v_n_1528_, v_reader_1529_);
lean_dec(v_n_1528_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___redArg(lean_object* v_size_1532_, lean_object* v_reader_1533_){
_start:
{
lean_object* v_input_1534_; lean_object* v_messageHead_1535_; lean_object* v_messageCount_1536_; lean_object* v_bodyBytesRead_1537_; lean_object* v_headerBytesRead_1538_; uint8_t v_noMoreInput_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1548_; 
v_input_1534_ = lean_ctor_get(v_reader_1533_, 1);
v_messageHead_1535_ = lean_ctor_get(v_reader_1533_, 2);
v_messageCount_1536_ = lean_ctor_get(v_reader_1533_, 3);
v_bodyBytesRead_1537_ = lean_ctor_get(v_reader_1533_, 4);
v_headerBytesRead_1538_ = lean_ctor_get(v_reader_1533_, 5);
v_noMoreInput_1539_ = lean_ctor_get_uint8(v_reader_1533_, sizeof(void*)*6);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_reader_1533_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_reader_1533_, 0);
lean_dec(v_unused_1549_);
v___x_1541_ = v_reader_1533_;
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_headerBytesRead_1538_);
lean_inc(v_bodyBytesRead_1537_);
lean_inc(v_messageCount_1536_);
lean_inc(v_messageHead_1535_);
lean_inc(v_input_1534_);
lean_dec(v_reader_1533_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1548_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v_size_1532_);
v___x_1544_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_input_1534_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_messageHead_1535_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_messageCount_1536_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_bodyBytesRead_1537_);
lean_ctor_set(v_reuseFailAlloc_1547_, 5, v_headerBytesRead_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*6, v_noMoreInput_1539_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody(uint8_t v_dir_1550_, lean_object* v_size_1551_, lean_object* v_reader_1552_){
_start:
{
lean_object* v_input_1553_; lean_object* v_messageHead_1554_; lean_object* v_messageCount_1555_; lean_object* v_bodyBytesRead_1556_; lean_object* v_headerBytesRead_1557_; uint8_t v_noMoreInput_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1567_; 
v_input_1553_ = lean_ctor_get(v_reader_1552_, 1);
v_messageHead_1554_ = lean_ctor_get(v_reader_1552_, 2);
v_messageCount_1555_ = lean_ctor_get(v_reader_1552_, 3);
v_bodyBytesRead_1556_ = lean_ctor_get(v_reader_1552_, 4);
v_headerBytesRead_1557_ = lean_ctor_get(v_reader_1552_, 5);
v_noMoreInput_1558_ = lean_ctor_get_uint8(v_reader_1552_, sizeof(void*)*6);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_reader_1552_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; 
v_unused_1568_ = lean_ctor_get(v_reader_1552_, 0);
lean_dec(v_unused_1568_);
v___x_1560_ = v_reader_1552_;
v_isShared_1561_ = v_isSharedCheck_1567_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_headerBytesRead_1557_);
lean_inc(v_bodyBytesRead_1556_);
lean_inc(v_messageCount_1555_);
lean_inc(v_messageHead_1554_);
lean_inc(v_input_1553_);
lean_dec(v_reader_1552_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1567_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_size_1551_);
v___x_1563_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1563_);
v___x_1565_ = v___x_1560_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_input_1553_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_messageHead_1554_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v_messageCount_1555_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v_bodyBytesRead_1556_);
lean_ctor_set(v_reuseFailAlloc_1566_, 5, v_headerBytesRead_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1566_, sizeof(void*)*6, v_noMoreInput_1558_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_startFixedBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1550_ = stack[0].m_num;
lean_object* v_size_1551_ = stack[1].m_obj;
lean_object* v_reader_1552_ = stack[2].m_obj;
lean_object* v_res_1569_;
v_res_1569_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_1550_, v_size_1551_, v_reader_1552_);
stack->m_obj
 = v_res_1569_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startFixedBody___boxed(lean_object* v_dir_1570_, lean_object* v_size_1571_, lean_object* v_reader_1572_){
_start:
{
uint8_t v_dir_boxed_1573_; lean_object* v_res_1574_; 
v_dir_boxed_1573_ = lean_unbox(v_dir_1570_);
v_res_1574_ = l_Std_Http_Protocol_H1_Reader_startFixedBody(v_dir_boxed_1573_, v_size_1571_, v_reader_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg(lean_object* v_reader_1577_){
_start:
{
lean_object* v_input_1578_; lean_object* v_messageHead_1579_; lean_object* v_messageCount_1580_; lean_object* v_bodyBytesRead_1581_; lean_object* v_headerBytesRead_1582_; uint8_t v_noMoreInput_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1591_; 
v_input_1578_ = lean_ctor_get(v_reader_1577_, 1);
v_messageHead_1579_ = lean_ctor_get(v_reader_1577_, 2);
v_messageCount_1580_ = lean_ctor_get(v_reader_1577_, 3);
v_bodyBytesRead_1581_ = lean_ctor_get(v_reader_1577_, 4);
v_headerBytesRead_1582_ = lean_ctor_get(v_reader_1577_, 5);
v_noMoreInput_1583_ = lean_ctor_get_uint8(v_reader_1577_, sizeof(void*)*6);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_reader_1577_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_reader_1577_, 0);
lean_dec(v_unused_1592_);
v___x_1585_ = v_reader_1577_;
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_headerBytesRead_1582_);
lean_inc(v_bodyBytesRead_1581_);
lean_inc(v_messageCount_1580_);
lean_inc(v_messageHead_1579_);
lean_inc(v_input_1578_);
lean_dec(v_reader_1577_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1587_);
v___x_1589_ = v___x_1585_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_input_1578_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_messageHead_1579_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_messageCount_1580_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_bodyBytesRead_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 5, v_headerBytesRead_1582_);
lean_ctor_set_uint8(v_reuseFailAlloc_1590_, sizeof(void*)*6, v_noMoreInput_1583_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody(uint8_t v_dir_1593_, lean_object* v_reader_1594_){
_start:
{
lean_object* v_input_1595_; lean_object* v_messageHead_1596_; lean_object* v_messageCount_1597_; lean_object* v_bodyBytesRead_1598_; lean_object* v_headerBytesRead_1599_; uint8_t v_noMoreInput_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
v_input_1595_ = lean_ctor_get(v_reader_1594_, 1);
v_messageHead_1596_ = lean_ctor_get(v_reader_1594_, 2);
v_messageCount_1597_ = lean_ctor_get(v_reader_1594_, 3);
v_bodyBytesRead_1598_ = lean_ctor_get(v_reader_1594_, 4);
v_headerBytesRead_1599_ = lean_ctor_get(v_reader_1594_, 5);
v_noMoreInput_1600_ = lean_ctor_get_uint8(v_reader_1594_, sizeof(void*)*6);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_reader_1594_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v_reader_1594_, 0);
lean_dec(v_unused_1609_);
v___x_1602_ = v_reader_1594_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_headerBytesRead_1599_);
lean_inc(v_bodyBytesRead_1598_);
lean_inc(v_messageCount_1597_);
lean_inc(v_messageHead_1596_);
lean_inc(v_input_1595_);
lean_dec(v_reader_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = ((lean_object*)(l_Std_Http_Protocol_H1_Reader_startChunkedBody___redArg___closed__0));
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_input_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_messageHead_1596_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_messageCount_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_bodyBytesRead_1598_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v_headerBytesRead_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*6, v_noMoreInput_1600_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_startChunkedBody_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1593_ = stack[0].m_num;
lean_object* v_reader_1594_ = stack[1].m_obj;
lean_object* v_res_1610_;
v_res_1610_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_1593_, v_reader_1594_);
stack->m_obj
 = v_res_1610_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_startChunkedBody___boxed(lean_object* v_dir_1611_, lean_object* v_reader_1612_){
_start:
{
uint8_t v_dir_boxed_1613_; lean_object* v_res_1614_; 
v_dir_boxed_1613_ = lean_unbox(v_dir_1611_);
v_res_1614_ = l_Std_Http_Protocol_H1_Reader_startChunkedBody(v_dir_boxed_1613_, v_reader_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___redArg(lean_object* v_reader_1615_){
_start:
{
lean_object* v_state_1616_; lean_object* v_input_1617_; lean_object* v_messageHead_1618_; lean_object* v_messageCount_1619_; lean_object* v_bodyBytesRead_1620_; lean_object* v_headerBytesRead_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
v_state_1616_ = lean_ctor_get(v_reader_1615_, 0);
v_input_1617_ = lean_ctor_get(v_reader_1615_, 1);
v_messageHead_1618_ = lean_ctor_get(v_reader_1615_, 2);
v_messageCount_1619_ = lean_ctor_get(v_reader_1615_, 3);
v_bodyBytesRead_1620_ = lean_ctor_get(v_reader_1615_, 4);
v_headerBytesRead_1621_ = lean_ctor_get(v_reader_1615_, 5);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_reader_1615_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v_reader_1615_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_headerBytesRead_1621_);
lean_inc(v_bodyBytesRead_1620_);
lean_inc(v_messageCount_1619_);
lean_inc(v_messageHead_1618_);
lean_inc(v_input_1617_);
lean_inc(v_state_1616_);
lean_dec(v_reader_1615_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
uint8_t v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = 1;
if (v_isShared_1624_ == 0)
{
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_state_1616_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_input_1617_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_messageHead_1618_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_messageCount_1619_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_bodyBytesRead_1620_);
lean_ctor_set(v_reuseFailAlloc_1628_, 5, v_headerBytesRead_1621_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*6, v___x_1625_);
return v___x_1627_;
}
}
}
}
lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput(uint8_t v_dir_1630_, lean_object* v_reader_1631_){
_start:
{
lean_object* v_state_1632_; lean_object* v_input_1633_; lean_object* v_messageHead_1634_; lean_object* v_messageCount_1635_; lean_object* v_bodyBytesRead_1636_; lean_object* v_headerBytesRead_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
v_state_1632_ = lean_ctor_get(v_reader_1631_, 0);
v_input_1633_ = lean_ctor_get(v_reader_1631_, 1);
v_messageHead_1634_ = lean_ctor_get(v_reader_1631_, 2);
v_messageCount_1635_ = lean_ctor_get(v_reader_1631_, 3);
v_bodyBytesRead_1636_ = lean_ctor_get(v_reader_1631_, 4);
v_headerBytesRead_1637_ = lean_ctor_get(v_reader_1631_, 5);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_reader_1631_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1639_ = v_reader_1631_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_headerBytesRead_1637_);
lean_inc(v_bodyBytesRead_1636_);
lean_inc(v_messageCount_1635_);
lean_inc(v_messageHead_1634_);
lean_inc(v_input_1633_);
lean_inc(v_state_1632_);
lean_dec(v_reader_1631_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
uint8_t v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = 1;
if (v_isShared_1640_ == 0)
{
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_state_1632_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_input_1633_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_messageHead_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_messageCount_1635_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_bodyBytesRead_1636_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_headerBytesRead_1637_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*6, v___x_1641_);
return v___x_1643_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_markNoMoreInput_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1630_ = stack[0].m_num;
lean_object* v_reader_1631_ = stack[1].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_1630_, v_reader_1631_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_markNoMoreInput___boxed(lean_object* v_dir_1647_, lean_object* v_reader_1648_){
_start:
{
uint8_t v_dir_boxed_1649_; lean_object* v_res_1650_; 
v_dir_boxed_1649_ = lean_unbox(v_dir_1647_);
v_res_1650_ = l_Std_Http_Protocol_H1_Reader_markNoMoreInput(v_dir_boxed_1649_, v_reader_1648_);
return v_res_1650_;
}
}
uint8_t l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(uint8_t v_dir_1651_, lean_object* v_reader_1652_){
_start:
{
lean_object* v_messageHead_1653_; uint8_t v___x_1654_; 
v_messageHead_1653_ = lean_ctor_get(v_reader_1652_, 2);
v___x_1654_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v_dir_1651_, v_messageHead_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT void l_Std_Http_Protocol_H1_Reader_shouldKeepAlive_0interp(lean_interpreter_value* stack)
{
uint8_t v_dir_1651_ = stack[0].m_num;
lean_object* v_reader_1652_ = stack[1].m_obj;
uint8_t v_res_1655_;
v_res_1655_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_1651_, v_reader_1652_);
stack->m_num = v_res_1655_;
}
LEAN_EXPORT lean_object* l_Std_Http_Protocol_H1_Reader_shouldKeepAlive___boxed(lean_object* v_dir_1656_, lean_object* v_reader_1657_){
_start:
{
uint8_t v_dir_boxed_1658_; uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_dir_boxed_1658_ = lean_unbox(v_dir_1656_);
v_res_1659_ = l_Std_Http_Protocol_H1_Reader_shouldKeepAlive(v_dir_boxed_1658_, v_reader_1657_);
lean_dec_ref(v_reader_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
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
